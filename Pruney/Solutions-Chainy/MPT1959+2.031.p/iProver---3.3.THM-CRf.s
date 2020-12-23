%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:30 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  224 (1452 expanded)
%              Number of clauses        :  126 ( 367 expanded)
%              Number of leaves         :   28 ( 289 expanded)
%              Depth                    :   27
%              Number of atoms          :  969 (11496 expanded)
%              Number of equality atoms :  219 ( 541 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f24,plain,(
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

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X2)
          | ~ r2_hidden(sK0(X0,X1,X2),X1) )
        & ( r2_hidden(sK0(X0,X1,X2),X2)
          | r2_hidden(sK0(X0,X1,X2),X1) )
        & m1_subset_1(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK0(X0,X1,X2),X2)
              | ~ r2_hidden(sK0(X0,X1,X2),X1) )
            & ( r2_hidden(sK0(X0,X1,X2),X2)
              | r2_hidden(sK0(X0,X1,X2),X1) )
            & m1_subset_1(sK0(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | m1_subset_1(sK0(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f19,plain,(
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
    inference(pure_predicate_removal,[],[f18])).

fof(f20,plain,(
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
    inference(pure_predicate_removal,[],[f19])).

fof(f21,plain,(
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
    inference(pure_predicate_removal,[],[f20])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f68,plain,(
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
    inference(flattening,[],[f67])).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( r2_hidden(k3_yellow_0(X0),sK7)
          | ~ v1_subset_1(sK7,u1_struct_0(X0)) )
        & ( ~ r2_hidden(k3_yellow_0(X0),sK7)
          | v1_subset_1(sK7,u1_struct_0(X0)) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK7,X0)
        & ~ v1_xboole_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
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
          ( ( r2_hidden(k3_yellow_0(sK6),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK6)) )
          & ( ~ r2_hidden(k3_yellow_0(sK6),X1)
            | v1_subset_1(X1,u1_struct_0(sK6)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
          & v13_waybel_0(X1,sK6)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK6)
      & v1_yellow_0(sK6)
      & v5_orders_2(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
    ( ( r2_hidden(k3_yellow_0(sK6),sK7)
      | ~ v1_subset_1(sK7,u1_struct_0(sK6)) )
    & ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
      | v1_subset_1(sK7,u1_struct_0(sK6)) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & v13_waybel_0(sK7,sK6)
    & ~ v1_xboole_0(sK7)
    & l1_orders_2(sK6)
    & v1_yellow_0(sK6)
    & v5_orders_2(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f68,f70,f69])).

fof(f110,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f71])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f61])).

fof(f64,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X2,X3)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r1_orders_2(X0,X2,sK5(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X2,X3)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,sK4(X0,X1),X3)
            & r2_hidden(sK4(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK5(X0,X1),X1)
                & r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1))
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f62,f64,f63])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f107,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f71])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
                & r2_hidden(sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f54])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f96,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f109,plain,(
    v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f71])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f56])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
                & r2_lattice3(X0,X1,sK3(X0,X1,X2))
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f58,f59])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f113,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f39,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f95,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f106,plain,(
    v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f71])).

fof(f104,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f71])).

fof(f105,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f71])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f87,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f112,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | ~ v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f71])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f108,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f71])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK1(X0),X0)
      & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f4,f50])).

fof(f78,plain,(
    ! [X0] : ~ v1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f111,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X1,X0,X2),X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2570,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(sK0(X2,X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2566,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2573,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3122,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2566,c_2573])).

cnf(c_27,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_37,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_920,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_37])).

cnf(c_921,plain,
    ( v13_waybel_0(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_920])).

cnf(c_2545,plain,
    ( v13_waybel_0(X0,sK6) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_921])).

cnf(c_14,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_839,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_37])).

cnf(c_840,plain,
    ( r1_orders_2(sK6,X0,X1)
    | ~ r2_lattice3(sK6,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X0,X2) ),
    inference(unflattening,[status(thm)],[c_839])).

cnf(c_2550,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r2_lattice3(sK6,X2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_840])).

cnf(c_3642,plain,
    ( r1_orders_2(sK6,sK5(sK6,X0),X1) = iProver_top
    | r2_lattice3(sK6,X2,X1) != iProver_top
    | v13_waybel_0(X0,sK6) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK5(sK6,X0),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_2550])).

cnf(c_9497,plain,
    ( r1_orders_2(sK6,sK5(sK6,X0),X1) = iProver_top
    | r2_lattice3(sK6,u1_struct_0(sK6),X1) != iProver_top
    | v13_waybel_0(X0,sK6) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK5(sK6,X0),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3122,c_3642])).

cnf(c_29,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_778,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_37])).

cnf(c_779,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(X2,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_778])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_795,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(X2,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_779,c_9])).

cnf(c_2554,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_795])).

cnf(c_4430,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2566,c_2554])).

cnf(c_47,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_35,negated_conjecture,
    ( v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1015,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK7 != X2
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_795])).

cnf(c_1016,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7) ),
    inference(unflattening,[status(thm)],[c_1015])).

cnf(c_1017,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(c_4780,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4430,c_47,c_1017])).

cnf(c_10695,plain,
    ( r2_lattice3(sK6,u1_struct_0(sK6),X0) != iProver_top
    | v13_waybel_0(X1,sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(sK5(sK6,X1),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_9497,c_4780])).

cnf(c_19,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_21,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_252,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_21])).

cnf(c_253,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_252])).

cnf(c_23,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_38,negated_conjecture,
    ( v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_578,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_38])).

cnf(c_579,plain,
    ( r1_yellow_0(sK6,k1_xboole_0)
    | v2_struct_0(sK6)
    | ~ v5_orders_2(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_39,negated_conjecture,
    ( v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_73,plain,
    ( r1_yellow_0(sK6,k1_xboole_0)
    | v2_struct_0(sK6)
    | ~ v5_orders_2(sK6)
    | ~ v1_yellow_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_581,plain,
    ( r1_yellow_0(sK6,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_579,c_40,c_39,c_38,c_37,c_73])).

cnf(c_677,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK6 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_253,c_581])).

cnf(c_678,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
    | ~ r2_lattice3(sK6,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_677])).

cnf(c_682,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_lattice3(sK6,k1_xboole_0,X0)
    | r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_678,c_37])).

cnf(c_683,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
    | ~ r2_lattice3(sK6,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_682])).

cnf(c_2558,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) = iProver_top
    | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_683])).

cnf(c_15,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_834,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_37])).

cnf(c_835,plain,
    ( k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
    inference(unflattening,[status(thm)],[c_834])).

cnf(c_2663,plain,
    ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
    | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2558,c_835])).

cnf(c_4789,plain,
    ( r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2663,c_4780])).

cnf(c_30,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_32,negated_conjecture,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_328,plain,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(prop_impl,[status(thm)],[c_32])).

cnf(c_615,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK6),sK7)
    | X1 = X0
    | u1_struct_0(sK6) != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_328])).

cnf(c_616,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(unflattening,[status(thm)],[c_615])).

cnf(c_618,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_616,c_34])).

cnf(c_2561,plain,
    ( u1_struct_0(sK6) = sK7
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_618])).

cnf(c_44,plain,
    ( l1_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_22,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_75,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_77,plain,
    ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_617,plain,
    ( u1_struct_0(sK6) = sK7
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_2014,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_2028,plain,
    ( k3_yellow_0(sK6) = k3_yellow_0(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2014])).

cnf(c_2004,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2035,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_2004])).

cnf(c_3041,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_2004])).

cnf(c_2005,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3008,plain,
    ( u1_struct_0(sK6) != X0
    | sK7 != X0
    | sK7 = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2005])).

cnf(c_3535,plain,
    ( u1_struct_0(sK6) != sK7
    | sK7 = u1_struct_0(sK6)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3008])).

cnf(c_2008,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2953,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
    | X0 != k3_yellow_0(sK6)
    | X1 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2008])).

cnf(c_3190,plain,
    ( m1_subset_1(k3_yellow_0(sK6),X0)
    | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
    | X0 != u1_struct_0(sK6)
    | k3_yellow_0(sK6) != k3_yellow_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2953])).

cnf(c_4198,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
    | m1_subset_1(k3_yellow_0(sK6),sK7)
    | k3_yellow_0(sK6) != k3_yellow_0(sK6)
    | sK7 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3190])).

cnf(c_4199,plain,
    ( k3_yellow_0(sK6) != k3_yellow_0(sK6)
    | sK7 != u1_struct_0(sK6)
    | m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4198])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_36])).

cnf(c_564,plain,
    ( ~ m1_subset_1(X0,sK7)
    | r2_hidden(X0,sK7) ),
    inference(unflattening,[status(thm)],[c_563])).

cnf(c_5171,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK6),sK7)
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_5172,plain,
    ( m1_subset_1(k3_yellow_0(sK6),sK7) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5171])).

cnf(c_5419,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2561,c_44,c_47,c_77,c_617,c_2028,c_2035,c_3041,c_3535,c_4199,c_5172])).

cnf(c_12,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_875,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_37])).

cnf(c_876,plain,
    ( r2_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(sK2(sK6,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_875])).

cnf(c_2548,plain,
    ( r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_876])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_552,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_553,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_2564,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_553])).

cnf(c_6806,plain,
    ( r2_lattice3(sK6,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2548,c_2564])).

cnf(c_10731,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10695,c_44,c_47,c_77,c_617,c_2028,c_2035,c_3041,c_3535,c_4199,c_4789,c_5172,c_6806])).

cnf(c_10732,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_10731])).

cnf(c_10740,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK6),X1,X0),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2570,c_10732])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X0,X2),X2)
    | ~ r2_hidden(sK0(X1,X0,X2),X0)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2572,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | r2_hidden(sK0(X2,X0,X1),X1) != iProver_top
    | r2_hidden(sK0(X2,X0,X1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3877,plain,
    ( u1_struct_0(sK6) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK0(X1,X0,u1_struct_0(sK6)),X0) != iProver_top
    | r2_hidden(sK0(X1,X0,u1_struct_0(sK6)),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3122,c_2572])).

cnf(c_11685,plain,
    ( u1_struct_0(sK6) = sK7
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_10740,c_3877])).

cnf(c_11690,plain,
    ( u1_struct_0(sK6) = sK7
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11685,c_10740])).

cnf(c_2943,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK1(X2),k1_zfmisc_1(X2))
    | X0 != sK1(X2)
    | X1 != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_2008])).

cnf(c_3069,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK1(X1),k1_zfmisc_1(X1))
    | X0 != sK1(X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2943])).

cnf(c_3559,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | X0 != sK1(u1_struct_0(sK6))
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3069])).

cnf(c_5851,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | u1_struct_0(sK6) != sK1(u1_struct_0(sK6))
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3559])).

cnf(c_5852,plain,
    ( u1_struct_0(sK6) != sK1(u1_struct_0(sK6))
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5851])).

cnf(c_3070,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_2004])).

cnf(c_3911,plain,
    ( k1_zfmisc_1(u1_struct_0(sK6)) = k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3070])).

cnf(c_5,plain,
    ( ~ v1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_592,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | X1 = X0
    | sK1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_30])).

cnf(c_593,plain,
    ( ~ m1_subset_1(sK1(X0),k1_zfmisc_1(X0))
    | X0 = sK1(X0) ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_6,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_597,plain,
    ( X0 = sK1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_593,c_6])).

cnf(c_3453,plain,
    ( u1_struct_0(sK6) = sK1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_597])).

cnf(c_2902,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2908,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2902])).

cnf(c_33,negated_conjecture,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_326,plain,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(prop_impl,[status(thm)],[c_33])).

cnf(c_603,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) != X0
    | sK1(X0) != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_326])).

cnf(c_604,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | sK1(u1_struct_0(sK6)) != sK7 ),
    inference(unflattening,[status(thm)],[c_603])).

cnf(c_2562,plain,
    ( sK1(u1_struct_0(sK6)) != sK7
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_604])).

cnf(c_2606,plain,
    ( u1_struct_0(sK6) != sK7
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2562,c_597])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11690,c_5852,c_5419,c_3911,c_3453,c_2908,c_2606,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n010.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:14:44 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.85/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.85/0.98  
% 3.85/0.98  ------  iProver source info
% 3.85/0.98  
% 3.85/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.85/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.85/0.98  git: non_committed_changes: false
% 3.85/0.98  git: last_make_outside_of_git: false
% 3.85/0.98  
% 3.85/0.98  ------ 
% 3.85/0.98  
% 3.85/0.98  ------ Input Options
% 3.85/0.98  
% 3.85/0.98  --out_options                           all
% 3.85/0.98  --tptp_safe_out                         true
% 3.85/0.98  --problem_path                          ""
% 3.85/0.98  --include_path                          ""
% 3.85/0.98  --clausifier                            res/vclausify_rel
% 3.85/0.98  --clausifier_options                    --mode clausify
% 3.85/0.98  --stdin                                 false
% 3.85/0.98  --stats_out                             all
% 3.85/0.98  
% 3.85/0.98  ------ General Options
% 3.85/0.98  
% 3.85/0.98  --fof                                   false
% 3.85/0.98  --time_out_real                         305.
% 3.85/0.98  --time_out_virtual                      -1.
% 3.85/0.98  --symbol_type_check                     false
% 3.85/0.98  --clausify_out                          false
% 3.85/0.98  --sig_cnt_out                           false
% 3.85/0.98  --trig_cnt_out                          false
% 3.85/0.98  --trig_cnt_out_tolerance                1.
% 3.85/0.98  --trig_cnt_out_sk_spl                   false
% 3.85/0.98  --abstr_cl_out                          false
% 3.85/0.98  
% 3.85/0.98  ------ Global Options
% 3.85/0.98  
% 3.85/0.98  --schedule                              default
% 3.85/0.98  --add_important_lit                     false
% 3.85/0.98  --prop_solver_per_cl                    1000
% 3.85/0.98  --min_unsat_core                        false
% 3.85/0.98  --soft_assumptions                      false
% 3.85/0.98  --soft_lemma_size                       3
% 3.85/0.98  --prop_impl_unit_size                   0
% 3.85/0.98  --prop_impl_unit                        []
% 3.85/0.98  --share_sel_clauses                     true
% 3.85/0.98  --reset_solvers                         false
% 3.85/0.98  --bc_imp_inh                            [conj_cone]
% 3.85/0.98  --conj_cone_tolerance                   3.
% 3.85/0.98  --extra_neg_conj                        none
% 3.85/0.98  --large_theory_mode                     true
% 3.85/0.98  --prolific_symb_bound                   200
% 3.85/0.98  --lt_threshold                          2000
% 3.85/0.98  --clause_weak_htbl                      true
% 3.85/0.98  --gc_record_bc_elim                     false
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing Options
% 3.85/0.98  
% 3.85/0.98  --preprocessing_flag                    true
% 3.85/0.98  --time_out_prep_mult                    0.1
% 3.85/0.98  --splitting_mode                        input
% 3.85/0.98  --splitting_grd                         true
% 3.85/0.98  --splitting_cvd                         false
% 3.85/0.98  --splitting_cvd_svl                     false
% 3.85/0.98  --splitting_nvd                         32
% 3.85/0.98  --sub_typing                            true
% 3.85/0.98  --prep_gs_sim                           true
% 3.85/0.98  --prep_unflatten                        true
% 3.85/0.98  --prep_res_sim                          true
% 3.85/0.98  --prep_upred                            true
% 3.85/0.98  --prep_sem_filter                       exhaustive
% 3.85/0.98  --prep_sem_filter_out                   false
% 3.85/0.98  --pred_elim                             true
% 3.85/0.98  --res_sim_input                         true
% 3.85/0.98  --eq_ax_congr_red                       true
% 3.85/0.98  --pure_diseq_elim                       true
% 3.85/0.98  --brand_transform                       false
% 3.85/0.98  --non_eq_to_eq                          false
% 3.85/0.98  --prep_def_merge                        true
% 3.85/0.98  --prep_def_merge_prop_impl              false
% 3.85/0.98  --prep_def_merge_mbd                    true
% 3.85/0.98  --prep_def_merge_tr_red                 false
% 3.85/0.98  --prep_def_merge_tr_cl                  false
% 3.85/0.98  --smt_preprocessing                     true
% 3.85/0.98  --smt_ac_axioms                         fast
% 3.85/0.98  --preprocessed_out                      false
% 3.85/0.98  --preprocessed_stats                    false
% 3.85/0.98  
% 3.85/0.98  ------ Abstraction refinement Options
% 3.85/0.98  
% 3.85/0.98  --abstr_ref                             []
% 3.85/0.98  --abstr_ref_prep                        false
% 3.85/0.98  --abstr_ref_until_sat                   false
% 3.85/0.98  --abstr_ref_sig_restrict                funpre
% 3.85/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/0.98  --abstr_ref_under                       []
% 3.85/0.98  
% 3.85/0.98  ------ SAT Options
% 3.85/0.98  
% 3.85/0.98  --sat_mode                              false
% 3.85/0.98  --sat_fm_restart_options                ""
% 3.85/0.98  --sat_gr_def                            false
% 3.85/0.98  --sat_epr_types                         true
% 3.85/0.98  --sat_non_cyclic_types                  false
% 3.85/0.98  --sat_finite_models                     false
% 3.85/0.98  --sat_fm_lemmas                         false
% 3.85/0.98  --sat_fm_prep                           false
% 3.85/0.98  --sat_fm_uc_incr                        true
% 3.85/0.98  --sat_out_model                         small
% 3.85/0.98  --sat_out_clauses                       false
% 3.85/0.98  
% 3.85/0.98  ------ QBF Options
% 3.85/0.98  
% 3.85/0.98  --qbf_mode                              false
% 3.85/0.98  --qbf_elim_univ                         false
% 3.85/0.98  --qbf_dom_inst                          none
% 3.85/0.98  --qbf_dom_pre_inst                      false
% 3.85/0.98  --qbf_sk_in                             false
% 3.85/0.98  --qbf_pred_elim                         true
% 3.85/0.98  --qbf_split                             512
% 3.85/0.98  
% 3.85/0.98  ------ BMC1 Options
% 3.85/0.98  
% 3.85/0.98  --bmc1_incremental                      false
% 3.85/0.98  --bmc1_axioms                           reachable_all
% 3.85/0.98  --bmc1_min_bound                        0
% 3.85/0.98  --bmc1_max_bound                        -1
% 3.85/0.98  --bmc1_max_bound_default                -1
% 3.85/0.98  --bmc1_symbol_reachability              true
% 3.85/0.98  --bmc1_property_lemmas                  false
% 3.85/0.98  --bmc1_k_induction                      false
% 3.85/0.98  --bmc1_non_equiv_states                 false
% 3.85/0.98  --bmc1_deadlock                         false
% 3.85/0.98  --bmc1_ucm                              false
% 3.85/0.98  --bmc1_add_unsat_core                   none
% 3.85/0.98  --bmc1_unsat_core_children              false
% 3.85/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/0.98  --bmc1_out_stat                         full
% 3.85/0.98  --bmc1_ground_init                      false
% 3.85/0.98  --bmc1_pre_inst_next_state              false
% 3.85/0.98  --bmc1_pre_inst_state                   false
% 3.85/0.98  --bmc1_pre_inst_reach_state             false
% 3.85/0.98  --bmc1_out_unsat_core                   false
% 3.85/0.98  --bmc1_aig_witness_out                  false
% 3.85/0.98  --bmc1_verbose                          false
% 3.85/0.98  --bmc1_dump_clauses_tptp                false
% 3.85/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.85/0.98  --bmc1_dump_file                        -
% 3.85/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.85/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.85/0.98  --bmc1_ucm_extend_mode                  1
% 3.85/0.98  --bmc1_ucm_init_mode                    2
% 3.85/0.98  --bmc1_ucm_cone_mode                    none
% 3.85/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.85/0.98  --bmc1_ucm_relax_model                  4
% 3.85/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.85/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/0.98  --bmc1_ucm_layered_model                none
% 3.85/0.98  --bmc1_ucm_max_lemma_size               10
% 3.85/0.98  
% 3.85/0.98  ------ AIG Options
% 3.85/0.98  
% 3.85/0.98  --aig_mode                              false
% 3.85/0.98  
% 3.85/0.98  ------ Instantiation Options
% 3.85/0.98  
% 3.85/0.98  --instantiation_flag                    true
% 3.85/0.98  --inst_sos_flag                         false
% 3.85/0.98  --inst_sos_phase                        true
% 3.85/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/0.98  --inst_lit_sel_side                     num_symb
% 3.85/0.98  --inst_solver_per_active                1400
% 3.85/0.98  --inst_solver_calls_frac                1.
% 3.85/0.98  --inst_passive_queue_type               priority_queues
% 3.85/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/0.98  --inst_passive_queues_freq              [25;2]
% 3.85/0.98  --inst_dismatching                      true
% 3.85/0.98  --inst_eager_unprocessed_to_passive     true
% 3.85/0.98  --inst_prop_sim_given                   true
% 3.85/0.98  --inst_prop_sim_new                     false
% 3.85/0.98  --inst_subs_new                         false
% 3.85/0.98  --inst_eq_res_simp                      false
% 3.85/0.98  --inst_subs_given                       false
% 3.85/0.98  --inst_orphan_elimination               true
% 3.85/0.98  --inst_learning_loop_flag               true
% 3.85/0.98  --inst_learning_start                   3000
% 3.85/0.98  --inst_learning_factor                  2
% 3.85/0.98  --inst_start_prop_sim_after_learn       3
% 3.85/0.98  --inst_sel_renew                        solver
% 3.85/0.98  --inst_lit_activity_flag                true
% 3.85/0.98  --inst_restr_to_given                   false
% 3.85/0.98  --inst_activity_threshold               500
% 3.85/0.98  --inst_out_proof                        true
% 3.85/0.98  
% 3.85/0.98  ------ Resolution Options
% 3.85/0.98  
% 3.85/0.98  --resolution_flag                       true
% 3.85/0.98  --res_lit_sel                           adaptive
% 3.85/0.98  --res_lit_sel_side                      none
% 3.85/0.98  --res_ordering                          kbo
% 3.85/0.98  --res_to_prop_solver                    active
% 3.85/0.98  --res_prop_simpl_new                    false
% 3.85/0.98  --res_prop_simpl_given                  true
% 3.85/0.98  --res_passive_queue_type                priority_queues
% 3.85/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/0.98  --res_passive_queues_freq               [15;5]
% 3.85/0.98  --res_forward_subs                      full
% 3.85/0.98  --res_backward_subs                     full
% 3.85/0.98  --res_forward_subs_resolution           true
% 3.85/0.98  --res_backward_subs_resolution          true
% 3.85/0.98  --res_orphan_elimination                true
% 3.85/0.98  --res_time_limit                        2.
% 3.85/0.98  --res_out_proof                         true
% 3.85/0.98  
% 3.85/0.98  ------ Superposition Options
% 3.85/0.98  
% 3.85/0.98  --superposition_flag                    true
% 3.85/0.98  --sup_passive_queue_type                priority_queues
% 3.85/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.85/0.98  --demod_completeness_check              fast
% 3.85/0.98  --demod_use_ground                      true
% 3.85/0.98  --sup_to_prop_solver                    passive
% 3.85/0.98  --sup_prop_simpl_new                    true
% 3.85/0.98  --sup_prop_simpl_given                  true
% 3.85/0.98  --sup_fun_splitting                     false
% 3.85/0.98  --sup_smt_interval                      50000
% 3.85/0.98  
% 3.85/0.98  ------ Superposition Simplification Setup
% 3.85/0.98  
% 3.85/0.98  --sup_indices_passive                   []
% 3.85/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/0.98  --sup_full_bw                           [BwDemod]
% 3.85/0.98  --sup_immed_triv                        [TrivRules]
% 3.85/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/0.98  --sup_immed_bw_main                     []
% 3.85/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.85/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.85/0.98  
% 3.85/0.98  ------ Combination Options
% 3.85/0.98  
% 3.85/0.98  --comb_res_mult                         3
% 3.85/0.98  --comb_sup_mult                         2
% 3.85/0.98  --comb_inst_mult                        10
% 3.85/0.98  
% 3.85/0.98  ------ Debug Options
% 3.85/0.98  
% 3.85/0.98  --dbg_backtrace                         false
% 3.85/0.98  --dbg_dump_prop_clauses                 false
% 3.85/0.98  --dbg_dump_prop_clauses_file            -
% 3.85/0.98  --dbg_out_stat                          false
% 3.85/0.98  ------ Parsing...
% 3.85/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  ------ Proving...
% 3.85/0.98  ------ Problem Properties 
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  clauses                                 33
% 3.85/0.98  conjectures                             2
% 3.85/0.98  EPR                                     4
% 3.85/0.98  Horn                                    22
% 3.85/0.98  unary                                   9
% 3.85/0.98  binary                                  4
% 3.85/0.98  lits                                    90
% 3.85/0.98  lits eq                                 11
% 3.85/0.98  fd_pure                                 0
% 3.85/0.98  fd_pseudo                               0
% 3.85/0.98  fd_cond                                 3
% 3.85/0.98  fd_pseudo_cond                          3
% 3.85/0.98  AC symbols                              0
% 3.85/0.98  
% 3.85/0.98  ------ Schedule dynamic 5 is on 
% 3.85/0.98  
% 3.85/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ 
% 3.85/0.98  Current options:
% 3.85/0.98  ------ 
% 3.85/0.98  
% 3.85/0.98  ------ Input Options
% 3.85/0.98  
% 3.85/0.98  --out_options                           all
% 3.85/0.98  --tptp_safe_out                         true
% 3.85/0.98  --problem_path                          ""
% 3.85/0.98  --include_path                          ""
% 3.85/0.98  --clausifier                            res/vclausify_rel
% 3.85/0.98  --clausifier_options                    --mode clausify
% 3.85/0.98  --stdin                                 false
% 3.85/0.98  --stats_out                             all
% 3.85/0.98  
% 3.85/0.98  ------ General Options
% 3.85/0.98  
% 3.85/0.98  --fof                                   false
% 3.85/0.98  --time_out_real                         305.
% 3.85/0.98  --time_out_virtual                      -1.
% 3.85/0.98  --symbol_type_check                     false
% 3.85/0.98  --clausify_out                          false
% 3.85/0.98  --sig_cnt_out                           false
% 3.85/0.98  --trig_cnt_out                          false
% 3.85/0.98  --trig_cnt_out_tolerance                1.
% 3.85/0.98  --trig_cnt_out_sk_spl                   false
% 3.85/0.98  --abstr_cl_out                          false
% 3.85/0.98  
% 3.85/0.98  ------ Global Options
% 3.85/0.98  
% 3.85/0.98  --schedule                              default
% 3.85/0.98  --add_important_lit                     false
% 3.85/0.98  --prop_solver_per_cl                    1000
% 3.85/0.98  --min_unsat_core                        false
% 3.85/0.98  --soft_assumptions                      false
% 3.85/0.98  --soft_lemma_size                       3
% 3.85/0.98  --prop_impl_unit_size                   0
% 3.85/0.98  --prop_impl_unit                        []
% 3.85/0.98  --share_sel_clauses                     true
% 3.85/0.98  --reset_solvers                         false
% 3.85/0.98  --bc_imp_inh                            [conj_cone]
% 3.85/0.98  --conj_cone_tolerance                   3.
% 3.85/0.98  --extra_neg_conj                        none
% 3.85/0.98  --large_theory_mode                     true
% 3.85/0.98  --prolific_symb_bound                   200
% 3.85/0.98  --lt_threshold                          2000
% 3.85/0.98  --clause_weak_htbl                      true
% 3.85/0.98  --gc_record_bc_elim                     false
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing Options
% 3.85/0.98  
% 3.85/0.98  --preprocessing_flag                    true
% 3.85/0.98  --time_out_prep_mult                    0.1
% 3.85/0.98  --splitting_mode                        input
% 3.85/0.98  --splitting_grd                         true
% 3.85/0.98  --splitting_cvd                         false
% 3.85/0.98  --splitting_cvd_svl                     false
% 3.85/0.98  --splitting_nvd                         32
% 3.85/0.98  --sub_typing                            true
% 3.85/0.98  --prep_gs_sim                           true
% 3.85/0.98  --prep_unflatten                        true
% 3.85/0.98  --prep_res_sim                          true
% 3.85/0.98  --prep_upred                            true
% 3.85/0.98  --prep_sem_filter                       exhaustive
% 3.85/0.98  --prep_sem_filter_out                   false
% 3.85/0.98  --pred_elim                             true
% 3.85/0.98  --res_sim_input                         true
% 3.85/0.98  --eq_ax_congr_red                       true
% 3.85/0.98  --pure_diseq_elim                       true
% 3.85/0.98  --brand_transform                       false
% 3.85/0.98  --non_eq_to_eq                          false
% 3.85/0.98  --prep_def_merge                        true
% 3.85/0.98  --prep_def_merge_prop_impl              false
% 3.85/0.98  --prep_def_merge_mbd                    true
% 3.85/0.98  --prep_def_merge_tr_red                 false
% 3.85/0.98  --prep_def_merge_tr_cl                  false
% 3.85/0.98  --smt_preprocessing                     true
% 3.85/0.98  --smt_ac_axioms                         fast
% 3.85/0.98  --preprocessed_out                      false
% 3.85/0.98  --preprocessed_stats                    false
% 3.85/0.98  
% 3.85/0.98  ------ Abstraction refinement Options
% 3.85/0.98  
% 3.85/0.98  --abstr_ref                             []
% 3.85/0.98  --abstr_ref_prep                        false
% 3.85/0.98  --abstr_ref_until_sat                   false
% 3.85/0.98  --abstr_ref_sig_restrict                funpre
% 3.85/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/0.98  --abstr_ref_under                       []
% 3.85/0.98  
% 3.85/0.98  ------ SAT Options
% 3.85/0.98  
% 3.85/0.98  --sat_mode                              false
% 3.85/0.98  --sat_fm_restart_options                ""
% 3.85/0.98  --sat_gr_def                            false
% 3.85/0.98  --sat_epr_types                         true
% 3.85/0.98  --sat_non_cyclic_types                  false
% 3.85/0.98  --sat_finite_models                     false
% 3.85/0.98  --sat_fm_lemmas                         false
% 3.85/0.98  --sat_fm_prep                           false
% 3.85/0.98  --sat_fm_uc_incr                        true
% 3.85/0.98  --sat_out_model                         small
% 3.85/0.98  --sat_out_clauses                       false
% 3.85/0.98  
% 3.85/0.98  ------ QBF Options
% 3.85/0.98  
% 3.85/0.98  --qbf_mode                              false
% 3.85/0.98  --qbf_elim_univ                         false
% 3.85/0.98  --qbf_dom_inst                          none
% 3.85/0.98  --qbf_dom_pre_inst                      false
% 3.85/0.98  --qbf_sk_in                             false
% 3.85/0.98  --qbf_pred_elim                         true
% 3.85/0.98  --qbf_split                             512
% 3.85/0.98  
% 3.85/0.98  ------ BMC1 Options
% 3.85/0.98  
% 3.85/0.98  --bmc1_incremental                      false
% 3.85/0.98  --bmc1_axioms                           reachable_all
% 3.85/0.98  --bmc1_min_bound                        0
% 3.85/0.98  --bmc1_max_bound                        -1
% 3.85/0.98  --bmc1_max_bound_default                -1
% 3.85/0.98  --bmc1_symbol_reachability              true
% 3.85/0.98  --bmc1_property_lemmas                  false
% 3.85/0.98  --bmc1_k_induction                      false
% 3.85/0.98  --bmc1_non_equiv_states                 false
% 3.85/0.98  --bmc1_deadlock                         false
% 3.85/0.98  --bmc1_ucm                              false
% 3.85/0.98  --bmc1_add_unsat_core                   none
% 3.85/0.98  --bmc1_unsat_core_children              false
% 3.85/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/0.98  --bmc1_out_stat                         full
% 3.85/0.98  --bmc1_ground_init                      false
% 3.85/0.98  --bmc1_pre_inst_next_state              false
% 3.85/0.98  --bmc1_pre_inst_state                   false
% 3.85/0.98  --bmc1_pre_inst_reach_state             false
% 3.85/0.98  --bmc1_out_unsat_core                   false
% 3.85/0.98  --bmc1_aig_witness_out                  false
% 3.85/0.98  --bmc1_verbose                          false
% 3.85/0.98  --bmc1_dump_clauses_tptp                false
% 3.85/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.85/0.98  --bmc1_dump_file                        -
% 3.85/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.85/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.85/0.98  --bmc1_ucm_extend_mode                  1
% 3.85/0.98  --bmc1_ucm_init_mode                    2
% 3.85/0.98  --bmc1_ucm_cone_mode                    none
% 3.85/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.85/0.98  --bmc1_ucm_relax_model                  4
% 3.85/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.85/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/0.98  --bmc1_ucm_layered_model                none
% 3.85/0.98  --bmc1_ucm_max_lemma_size               10
% 3.85/0.98  
% 3.85/0.98  ------ AIG Options
% 3.85/0.98  
% 3.85/0.98  --aig_mode                              false
% 3.85/0.98  
% 3.85/0.98  ------ Instantiation Options
% 3.85/0.98  
% 3.85/0.98  --instantiation_flag                    true
% 3.85/0.98  --inst_sos_flag                         false
% 3.85/0.98  --inst_sos_phase                        true
% 3.85/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/0.98  --inst_lit_sel_side                     none
% 3.85/0.98  --inst_solver_per_active                1400
% 3.85/0.98  --inst_solver_calls_frac                1.
% 3.85/0.98  --inst_passive_queue_type               priority_queues
% 3.85/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/0.98  --inst_passive_queues_freq              [25;2]
% 3.85/0.98  --inst_dismatching                      true
% 3.85/0.98  --inst_eager_unprocessed_to_passive     true
% 3.85/0.98  --inst_prop_sim_given                   true
% 3.85/0.98  --inst_prop_sim_new                     false
% 3.85/0.98  --inst_subs_new                         false
% 3.85/0.98  --inst_eq_res_simp                      false
% 3.85/0.98  --inst_subs_given                       false
% 3.85/0.98  --inst_orphan_elimination               true
% 3.85/0.98  --inst_learning_loop_flag               true
% 3.85/0.98  --inst_learning_start                   3000
% 3.85/0.98  --inst_learning_factor                  2
% 3.85/0.98  --inst_start_prop_sim_after_learn       3
% 3.85/0.98  --inst_sel_renew                        solver
% 3.85/0.98  --inst_lit_activity_flag                true
% 3.85/0.98  --inst_restr_to_given                   false
% 3.85/0.98  --inst_activity_threshold               500
% 3.85/0.98  --inst_out_proof                        true
% 3.85/0.98  
% 3.85/0.98  ------ Resolution Options
% 3.85/0.98  
% 3.85/0.98  --resolution_flag                       false
% 3.85/0.98  --res_lit_sel                           adaptive
% 3.85/0.98  --res_lit_sel_side                      none
% 3.85/0.98  --res_ordering                          kbo
% 3.85/0.98  --res_to_prop_solver                    active
% 3.85/0.98  --res_prop_simpl_new                    false
% 3.85/0.98  --res_prop_simpl_given                  true
% 3.85/0.98  --res_passive_queue_type                priority_queues
% 3.85/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/0.98  --res_passive_queues_freq               [15;5]
% 3.85/0.98  --res_forward_subs                      full
% 3.85/0.98  --res_backward_subs                     full
% 3.85/0.98  --res_forward_subs_resolution           true
% 3.85/0.98  --res_backward_subs_resolution          true
% 3.85/0.98  --res_orphan_elimination                true
% 3.85/0.98  --res_time_limit                        2.
% 3.85/0.98  --res_out_proof                         true
% 3.85/0.98  
% 3.85/0.98  ------ Superposition Options
% 3.85/0.98  
% 3.85/0.98  --superposition_flag                    true
% 3.85/0.98  --sup_passive_queue_type                priority_queues
% 3.85/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.85/0.98  --demod_completeness_check              fast
% 3.85/0.98  --demod_use_ground                      true
% 3.85/0.98  --sup_to_prop_solver                    passive
% 3.85/0.98  --sup_prop_simpl_new                    true
% 3.85/0.98  --sup_prop_simpl_given                  true
% 3.85/0.98  --sup_fun_splitting                     false
% 3.85/0.98  --sup_smt_interval                      50000
% 3.85/0.98  
% 3.85/0.98  ------ Superposition Simplification Setup
% 3.85/0.98  
% 3.85/0.98  --sup_indices_passive                   []
% 3.85/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/0.98  --sup_full_bw                           [BwDemod]
% 3.85/0.98  --sup_immed_triv                        [TrivRules]
% 3.85/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/0.98  --sup_immed_bw_main                     []
% 3.85/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.85/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.85/0.98  
% 3.85/0.98  ------ Combination Options
% 3.85/0.98  
% 3.85/0.98  --comb_res_mult                         3
% 3.85/0.98  --comb_sup_mult                         2
% 3.85/0.98  --comb_inst_mult                        10
% 3.85/0.98  
% 3.85/0.98  ------ Debug Options
% 3.85/0.98  
% 3.85/0.98  --dbg_backtrace                         false
% 3.85/0.98  --dbg_dump_prop_clauses                 false
% 3.85/0.98  --dbg_dump_prop_clauses_file            -
% 3.85/0.98  --dbg_out_stat                          false
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  % SZS status Theorem for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  fof(f3,axiom,(
% 3.85/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f24,plain,(
% 3.85/0.98    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/0.98    inference(ennf_transformation,[],[f3])).
% 3.85/0.98  
% 3.85/0.98  fof(f25,plain,(
% 3.85/0.98    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/0.98    inference(flattening,[],[f24])).
% 3.85/0.98  
% 3.85/0.98  fof(f46,plain,(
% 3.85/0.98    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/0.98    inference(nnf_transformation,[],[f25])).
% 3.85/0.98  
% 3.85/0.98  fof(f47,plain,(
% 3.85/0.98    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/0.98    inference(flattening,[],[f46])).
% 3.85/0.98  
% 3.85/0.98  fof(f48,plain,(
% 3.85/0.98    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK0(X0,X1,X2),X2) | ~r2_hidden(sK0(X0,X1,X2),X1)) & (r2_hidden(sK0(X0,X1,X2),X2) | r2_hidden(sK0(X0,X1,X2),X1)) & m1_subset_1(sK0(X0,X1,X2),X0)))),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f49,plain,(
% 3.85/0.98    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK0(X0,X1,X2),X2) | ~r2_hidden(sK0(X0,X1,X2),X1)) & (r2_hidden(sK0(X0,X1,X2),X2) | r2_hidden(sK0(X0,X1,X2),X1)) & m1_subset_1(sK0(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 3.85/0.98  
% 3.85/0.98  fof(f74,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (X1 = X2 | m1_subset_1(sK0(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f49])).
% 3.85/0.98  
% 3.85/0.98  fof(f17,conjecture,(
% 3.85/0.98    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f18,negated_conjecture,(
% 3.85/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.85/0.98    inference(negated_conjecture,[],[f17])).
% 3.85/0.98  
% 3.85/0.98  fof(f19,plain,(
% 3.85/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.85/0.98    inference(pure_predicate_removal,[],[f18])).
% 3.85/0.98  
% 3.85/0.98  fof(f20,plain,(
% 3.85/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.85/0.98    inference(pure_predicate_removal,[],[f19])).
% 3.85/0.98  
% 3.85/0.98  fof(f21,plain,(
% 3.85/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.85/0.98    inference(pure_predicate_removal,[],[f20])).
% 3.85/0.98  
% 3.85/0.98  fof(f44,plain,(
% 3.85/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.85/0.98    inference(ennf_transformation,[],[f21])).
% 3.85/0.98  
% 3.85/0.98  fof(f45,plain,(
% 3.85/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.85/0.98    inference(flattening,[],[f44])).
% 3.85/0.98  
% 3.85/0.98  fof(f67,plain,(
% 3.85/0.98    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.85/0.98    inference(nnf_transformation,[],[f45])).
% 3.85/0.98  
% 3.85/0.98  fof(f68,plain,(
% 3.85/0.98    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.85/0.98    inference(flattening,[],[f67])).
% 3.85/0.98  
% 3.85/0.98  fof(f70,plain,(
% 3.85/0.98    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK7) | ~v1_subset_1(sK7,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK7) | v1_subset_1(sK7,u1_struct_0(X0))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK7,X0) & ~v1_xboole_0(sK7))) )),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f69,plain,(
% 3.85/0.98    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK6),X1) | ~v1_subset_1(X1,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),X1) | v1_subset_1(X1,u1_struct_0(sK6))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(X1,sK6) & ~v1_xboole_0(X1)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & ~v2_struct_0(sK6))),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f71,plain,(
% 3.85/0.98    ((r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(sK7,sK6) & ~v1_xboole_0(sK7)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & ~v2_struct_0(sK6)),
% 3.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f68,f70,f69])).
% 3.85/0.98  
% 3.85/0.98  fof(f110,plain,(
% 3.85/0.98    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 3.85/0.98    inference(cnf_transformation,[],[f71])).
% 3.85/0.98  
% 3.85/0.98  fof(f2,axiom,(
% 3.85/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f23,plain,(
% 3.85/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/0.98    inference(ennf_transformation,[],[f2])).
% 3.85/0.98  
% 3.85/0.98  fof(f73,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f23])).
% 3.85/0.98  
% 3.85/0.98  fof(f15,axiom,(
% 3.85/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f41,plain,(
% 3.85/0.98    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(ennf_transformation,[],[f15])).
% 3.85/0.98  
% 3.85/0.98  fof(f42,plain,(
% 3.85/0.98    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(flattening,[],[f41])).
% 3.85/0.98  
% 3.85/0.98  fof(f61,plain,(
% 3.85/0.98    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(nnf_transformation,[],[f42])).
% 3.85/0.98  
% 3.85/0.98  fof(f62,plain,(
% 3.85/0.98    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(rectify,[],[f61])).
% 3.85/0.98  
% 3.85/0.98  fof(f64,plain,(
% 3.85/0.98    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,X2,sK5(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))) )),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f63,plain,(
% 3.85/0.98    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f65,plain,(
% 3.85/0.98    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f62,f64,f63])).
% 3.85/0.98  
% 3.85/0.98  fof(f98,plain,(
% 3.85/0.98    ( ! [X0,X1] : (v13_waybel_0(X1,X0) | m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f65])).
% 3.85/0.98  
% 3.85/0.98  fof(f107,plain,(
% 3.85/0.98    l1_orders_2(sK6)),
% 3.85/0.98    inference(cnf_transformation,[],[f71])).
% 3.85/0.98  
% 3.85/0.98  fof(f9,axiom,(
% 3.85/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f32,plain,(
% 3.85/0.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(ennf_transformation,[],[f9])).
% 3.85/0.98  
% 3.85/0.98  fof(f33,plain,(
% 3.85/0.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(flattening,[],[f32])).
% 3.85/0.98  
% 3.85/0.98  fof(f52,plain,(
% 3.85/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(nnf_transformation,[],[f33])).
% 3.85/0.98  
% 3.85/0.98  fof(f53,plain,(
% 3.85/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(rectify,[],[f52])).
% 3.85/0.98  
% 3.85/0.98  fof(f54,plain,(
% 3.85/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f55,plain,(
% 3.85/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f54])).
% 3.85/0.98  
% 3.85/0.98  fof(f83,plain,(
% 3.85/0.98    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f55])).
% 3.85/0.98  
% 3.85/0.98  fof(f96,plain,(
% 3.85/0.98    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f65])).
% 3.85/0.98  
% 3.85/0.98  fof(f7,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f29,plain,(
% 3.85/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.85/0.98    inference(ennf_transformation,[],[f7])).
% 3.85/0.98  
% 3.85/0.98  fof(f30,plain,(
% 3.85/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.85/0.98    inference(flattening,[],[f29])).
% 3.85/0.98  
% 3.85/0.98  fof(f81,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f30])).
% 3.85/0.98  
% 3.85/0.98  fof(f109,plain,(
% 3.85/0.98    v13_waybel_0(sK7,sK6)),
% 3.85/0.98    inference(cnf_transformation,[],[f71])).
% 3.85/0.98  
% 3.85/0.98  fof(f11,axiom,(
% 3.85/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f35,plain,(
% 3.85/0.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(ennf_transformation,[],[f11])).
% 3.85/0.98  
% 3.85/0.98  fof(f36,plain,(
% 3.85/0.98    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(flattening,[],[f35])).
% 3.85/0.98  
% 3.85/0.98  fof(f56,plain,(
% 3.85/0.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(nnf_transformation,[],[f36])).
% 3.85/0.98  
% 3.85/0.98  fof(f57,plain,(
% 3.85/0.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(flattening,[],[f56])).
% 3.85/0.98  
% 3.85/0.98  fof(f58,plain,(
% 3.85/0.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(rectify,[],[f57])).
% 3.85/0.98  
% 3.85/0.98  fof(f59,plain,(
% 3.85/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) & r2_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f60,plain,(
% 3.85/0.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) & r2_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f58,f59])).
% 3.85/0.98  
% 3.85/0.98  fof(f89,plain,(
% 3.85/0.98    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f60])).
% 3.85/0.98  
% 3.85/0.98  fof(f113,plain,(
% 3.85/0.98    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.85/0.98    inference(equality_resolution,[],[f89])).
% 3.85/0.98  
% 3.85/0.98  fof(f12,axiom,(
% 3.85/0.98    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f37,plain,(
% 3.85/0.98    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(ennf_transformation,[],[f12])).
% 3.85/0.98  
% 3.85/0.98  fof(f93,plain,(
% 3.85/0.98    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f37])).
% 3.85/0.98  
% 3.85/0.98  fof(f14,axiom,(
% 3.85/0.98    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f22,plain,(
% 3.85/0.98    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 3.85/0.98    inference(pure_predicate_removal,[],[f14])).
% 3.85/0.98  
% 3.85/0.98  fof(f39,plain,(
% 3.85/0.98    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.85/0.98    inference(ennf_transformation,[],[f22])).
% 3.85/0.98  
% 3.85/0.98  fof(f40,plain,(
% 3.85/0.98    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.85/0.98    inference(flattening,[],[f39])).
% 3.85/0.98  
% 3.85/0.98  fof(f95,plain,(
% 3.85/0.98    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f40])).
% 3.85/0.98  
% 3.85/0.98  fof(f106,plain,(
% 3.85/0.98    v1_yellow_0(sK6)),
% 3.85/0.98    inference(cnf_transformation,[],[f71])).
% 3.85/0.98  
% 3.85/0.98  fof(f104,plain,(
% 3.85/0.98    ~v2_struct_0(sK6)),
% 3.85/0.98    inference(cnf_transformation,[],[f71])).
% 3.85/0.98  
% 3.85/0.98  fof(f105,plain,(
% 3.85/0.98    v5_orders_2(sK6)),
% 3.85/0.98    inference(cnf_transformation,[],[f71])).
% 3.85/0.98  
% 3.85/0.98  fof(f10,axiom,(
% 3.85/0.98    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f34,plain,(
% 3.85/0.98    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(ennf_transformation,[],[f10])).
% 3.85/0.98  
% 3.85/0.98  fof(f87,plain,(
% 3.85/0.98    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f34])).
% 3.85/0.98  
% 3.85/0.98  fof(f16,axiom,(
% 3.85/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f43,plain,(
% 3.85/0.98    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/0.98    inference(ennf_transformation,[],[f16])).
% 3.85/0.98  
% 3.85/0.98  fof(f66,plain,(
% 3.85/0.98    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/0.98    inference(nnf_transformation,[],[f43])).
% 3.85/0.98  
% 3.85/0.98  fof(f103,plain,(
% 3.85/0.98    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f66])).
% 3.85/0.98  
% 3.85/0.98  fof(f112,plain,(
% 3.85/0.98    r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))),
% 3.85/0.98    inference(cnf_transformation,[],[f71])).
% 3.85/0.98  
% 3.85/0.98  fof(f13,axiom,(
% 3.85/0.98    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f38,plain,(
% 3.85/0.98    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.85/0.98    inference(ennf_transformation,[],[f13])).
% 3.85/0.98  
% 3.85/0.98  fof(f94,plain,(
% 3.85/0.98    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f38])).
% 3.85/0.98  
% 3.85/0.98  fof(f6,axiom,(
% 3.85/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f27,plain,(
% 3.85/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.85/0.98    inference(ennf_transformation,[],[f6])).
% 3.85/0.98  
% 3.85/0.98  fof(f28,plain,(
% 3.85/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.85/0.98    inference(flattening,[],[f27])).
% 3.85/0.98  
% 3.85/0.98  fof(f80,plain,(
% 3.85/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f28])).
% 3.85/0.98  
% 3.85/0.98  fof(f108,plain,(
% 3.85/0.98    ~v1_xboole_0(sK7)),
% 3.85/0.98    inference(cnf_transformation,[],[f71])).
% 3.85/0.98  
% 3.85/0.98  fof(f85,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f55])).
% 3.85/0.98  
% 3.85/0.98  fof(f1,axiom,(
% 3.85/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f72,plain,(
% 3.85/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f1])).
% 3.85/0.98  
% 3.85/0.98  fof(f8,axiom,(
% 3.85/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f31,plain,(
% 3.85/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.85/0.98    inference(ennf_transformation,[],[f8])).
% 3.85/0.98  
% 3.85/0.98  fof(f82,plain,(
% 3.85/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f31])).
% 3.85/0.98  
% 3.85/0.98  fof(f76,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(sK0(X0,X1,X2),X2) | ~r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f49])).
% 3.85/0.98  
% 3.85/0.98  fof(f4,axiom,(
% 3.85/0.98    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f50,plain,(
% 3.85/0.98    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0))))),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f51,plain,(
% 3.85/0.98    ! [X0] : (~v1_subset_1(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)))),
% 3.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f4,f50])).
% 3.85/0.98  
% 3.85/0.98  fof(f78,plain,(
% 3.85/0.98    ( ! [X0] : (~v1_subset_1(sK1(X0),X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f51])).
% 3.85/0.98  
% 3.85/0.98  fof(f77,plain,(
% 3.85/0.98    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(X0))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f51])).
% 3.85/0.98  
% 3.85/0.98  fof(f111,plain,(
% 3.85/0.98    ~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))),
% 3.85/0.98    inference(cnf_transformation,[],[f71])).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.85/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.85/0.98      | m1_subset_1(sK0(X1,X0,X2),X1)
% 3.85/0.98      | X0 = X2 ),
% 3.85/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2570,plain,
% 3.85/0.98      ( X0 = X1
% 3.85/0.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.85/0.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.85/0.98      | m1_subset_1(sK0(X2,X0,X1),X2) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_34,negated_conjecture,
% 3.85/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.85/0.98      inference(cnf_transformation,[],[f110]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2566,plain,
% 3.85/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.85/0.98      | ~ r2_hidden(X2,X0)
% 3.85/0.98      | r2_hidden(X2,X1) ),
% 3.85/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2573,plain,
% 3.85/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.85/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.85/0.98      | r2_hidden(X2,X1) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3122,plain,
% 3.85/0.98      ( r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
% 3.85/0.98      | r2_hidden(X0,sK7) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2566,c_2573]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_27,plain,
% 3.85/0.98      ( v13_waybel_0(X0,X1)
% 3.85/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/0.98      | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
% 3.85/0.98      | ~ l1_orders_2(X1) ),
% 3.85/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_37,negated_conjecture,
% 3.85/0.98      ( l1_orders_2(sK6) ),
% 3.85/0.98      inference(cnf_transformation,[],[f107]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_920,plain,
% 3.85/0.98      ( v13_waybel_0(X0,X1)
% 3.85/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/0.98      | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
% 3.85/0.98      | sK6 != X1 ),
% 3.85/0.98      inference(resolution_lifted,[status(thm)],[c_27,c_37]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_921,plain,
% 3.85/0.98      ( v13_waybel_0(X0,sK6)
% 3.85/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.85/0.98      | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6)) ),
% 3.85/0.98      inference(unflattening,[status(thm)],[c_920]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2545,plain,
% 3.85/0.98      ( v13_waybel_0(X0,sK6) = iProver_top
% 3.85/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.85/0.98      | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_921]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_14,plain,
% 3.85/0.98      ( r1_orders_2(X0,X1,X2)
% 3.85/0.98      | ~ r2_lattice3(X0,X3,X2)
% 3.85/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.85/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.85/0.98      | ~ r2_hidden(X1,X3)
% 3.85/0.98      | ~ l1_orders_2(X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_839,plain,
% 3.85/0.98      ( r1_orders_2(X0,X1,X2)
% 3.85/0.98      | ~ r2_lattice3(X0,X3,X2)
% 3.85/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.85/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.85/0.98      | ~ r2_hidden(X1,X3)
% 3.85/0.98      | sK6 != X0 ),
% 3.85/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_37]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_840,plain,
% 3.85/0.98      ( r1_orders_2(sK6,X0,X1)
% 3.85/0.98      | ~ r2_lattice3(sK6,X2,X1)
% 3.85/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.85/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.85/0.98      | ~ r2_hidden(X0,X2) ),
% 3.85/0.98      inference(unflattening,[status(thm)],[c_839]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2550,plain,
% 3.85/0.98      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 3.85/0.98      | r2_lattice3(sK6,X2,X1) != iProver_top
% 3.85/0.98      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.85/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.85/0.98      | r2_hidden(X0,X2) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_840]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3642,plain,
% 3.85/0.98      ( r1_orders_2(sK6,sK5(sK6,X0),X1) = iProver_top
% 3.85/0.98      | r2_lattice3(sK6,X2,X1) != iProver_top
% 3.85/0.98      | v13_waybel_0(X0,sK6) = iProver_top
% 3.85/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.85/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.85/0.98      | r2_hidden(sK5(sK6,X0),X2) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2545,c_2550]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_9497,plain,
% 3.85/0.98      ( r1_orders_2(sK6,sK5(sK6,X0),X1) = iProver_top
% 3.85/0.98      | r2_lattice3(sK6,u1_struct_0(sK6),X1) != iProver_top
% 3.85/0.98      | v13_waybel_0(X0,sK6) = iProver_top
% 3.85/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.85/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.85/0.98      | r2_hidden(sK5(sK6,X0),sK7) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_3122,c_3642]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_29,plain,
% 3.85/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 3.85/0.98      | ~ v13_waybel_0(X3,X0)
% 3.85/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.85/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.85/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.85/0.98      | ~ r2_hidden(X1,X3)
% 3.85/0.98      | r2_hidden(X2,X3)
% 3.85/0.98      | ~ l1_orders_2(X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_778,plain,
% 3.85/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 3.85/0.98      | ~ v13_waybel_0(X3,X0)
% 3.85/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.85/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.85/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.85/0.98      | ~ r2_hidden(X1,X3)
% 3.85/0.98      | r2_hidden(X2,X3)
% 3.85/0.98      | sK6 != X0 ),
% 3.85/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_37]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_779,plain,
% 3.85/0.98      ( ~ r1_orders_2(sK6,X0,X1)
% 3.85/0.98      | ~ v13_waybel_0(X2,sK6)
% 3.85/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.85/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.85/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.85/0.98      | ~ r2_hidden(X0,X2)
% 3.85/0.98      | r2_hidden(X1,X2) ),
% 3.85/0.98      inference(unflattening,[status(thm)],[c_778]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_9,plain,
% 3.85/0.98      ( m1_subset_1(X0,X1)
% 3.85/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.85/0.98      | ~ r2_hidden(X0,X2) ),
% 3.85/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_795,plain,
% 3.85/0.98      ( ~ r1_orders_2(sK6,X0,X1)
% 3.85/0.98      | ~ v13_waybel_0(X2,sK6)
% 3.85/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.85/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.85/0.98      | ~ r2_hidden(X0,X2)
% 3.85/0.98      | r2_hidden(X1,X2) ),
% 3.85/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_779,c_9]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2554,plain,
% 3.85/0.98      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.85/0.98      | v13_waybel_0(X2,sK6) != iProver_top
% 3.85/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.85/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.85/0.98      | r2_hidden(X0,X2) != iProver_top
% 3.85/0.98      | r2_hidden(X1,X2) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_795]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4430,plain,
% 3.85/0.98      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.85/0.98      | v13_waybel_0(sK7,sK6) != iProver_top
% 3.85/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.85/0.98      | r2_hidden(X0,sK7) != iProver_top
% 3.85/0.98      | r2_hidden(X1,sK7) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2566,c_2554]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_47,plain,
% 3.85/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_35,negated_conjecture,
% 3.85/0.98      ( v13_waybel_0(sK7,sK6) ),
% 3.85/0.98      inference(cnf_transformation,[],[f109]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1015,plain,
% 3.85/0.98      ( ~ r1_orders_2(sK6,X0,X1)
% 3.85/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.85/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.85/0.98      | ~ r2_hidden(X0,X2)
% 3.85/0.98      | r2_hidden(X1,X2)
% 3.85/0.98      | sK7 != X2
% 3.85/0.98      | sK6 != sK6 ),
% 3.85/0.98      inference(resolution_lifted,[status(thm)],[c_35,c_795]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1016,plain,
% 3.85/0.98      ( ~ r1_orders_2(sK6,X0,X1)
% 3.85/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.85/0.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.85/0.98      | ~ r2_hidden(X0,sK7)
% 3.85/0.98      | r2_hidden(X1,sK7) ),
% 3.85/0.98      inference(unflattening,[status(thm)],[c_1015]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1017,plain,
% 3.85/0.98      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.85/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.85/0.98      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.85/0.98      | r2_hidden(X0,sK7) != iProver_top
% 3.85/0.98      | r2_hidden(X1,sK7) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_1016]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4780,plain,
% 3.85/0.98      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.85/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.85/0.98      | r2_hidden(X0,sK7) != iProver_top
% 3.85/0.98      | r2_hidden(X1,sK7) = iProver_top ),
% 3.85/0.98      inference(global_propositional_subsumption,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_4430,c_47,c_1017]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_10695,plain,
% 3.85/0.98      ( r2_lattice3(sK6,u1_struct_0(sK6),X0) != iProver_top
% 3.85/0.98      | v13_waybel_0(X1,sK6) = iProver_top
% 3.85/0.98      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.85/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.85/0.98      | r2_hidden(X0,sK7) = iProver_top
% 3.85/0.98      | r2_hidden(sK5(sK6,X1),sK7) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_9497,c_4780]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_19,plain,
% 3.85/0.98      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.85/0.98      | ~ r2_lattice3(X0,X1,X2)
% 3.85/0.98      | ~ r1_yellow_0(X0,X1)
% 3.85/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.85/0.98      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.85/0.98      | ~ l1_orders_2(X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f113]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_21,plain,
% 3.85/0.98      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.85/0.98      | ~ l1_orders_2(X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_252,plain,
% 3.85/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.85/0.98      | ~ r1_yellow_0(X0,X1)
% 3.85/0.98      | ~ r2_lattice3(X0,X1,X2)
% 3.85/0.98      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.85/0.98      | ~ l1_orders_2(X0) ),
% 3.85/0.98      inference(global_propositional_subsumption,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_19,c_21]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_253,plain,
% 3.85/0.98      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.85/0.98      | ~ r2_lattice3(X0,X1,X2)
% 3.85/0.98      | ~ r1_yellow_0(X0,X1)
% 3.85/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.85/0.98      | ~ l1_orders_2(X0) ),
% 3.85/0.98      inference(renaming,[status(thm)],[c_252]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_23,plain,
% 3.85/0.98      ( r1_yellow_0(X0,k1_xboole_0)
% 3.85/0.98      | v2_struct_0(X0)
% 3.85/0.98      | ~ v5_orders_2(X0)
% 3.85/0.98      | ~ v1_yellow_0(X0)
% 3.85/0.98      | ~ l1_orders_2(X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_38,negated_conjecture,
% 3.85/0.98      ( v1_yellow_0(sK6) ),
% 3.85/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_578,plain,
% 3.85/0.98      ( r1_yellow_0(X0,k1_xboole_0)
% 3.85/0.98      | v2_struct_0(X0)
% 3.85/0.98      | ~ v5_orders_2(X0)
% 3.85/0.98      | ~ l1_orders_2(X0)
% 3.85/0.98      | sK6 != X0 ),
% 3.85/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_38]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_579,plain,
% 3.85/0.98      ( r1_yellow_0(sK6,k1_xboole_0)
% 3.85/0.98      | v2_struct_0(sK6)
% 3.85/0.98      | ~ v5_orders_2(sK6)
% 3.85/0.98      | ~ l1_orders_2(sK6) ),
% 3.85/0.98      inference(unflattening,[status(thm)],[c_578]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_40,negated_conjecture,
% 3.85/0.98      ( ~ v2_struct_0(sK6) ),
% 3.85/0.98      inference(cnf_transformation,[],[f104]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_39,negated_conjecture,
% 3.85/0.98      ( v5_orders_2(sK6) ),
% 3.85/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_73,plain,
% 3.85/0.98      ( r1_yellow_0(sK6,k1_xboole_0)
% 3.85/0.98      | v2_struct_0(sK6)
% 3.85/0.98      | ~ v5_orders_2(sK6)
% 3.85/0.98      | ~ v1_yellow_0(sK6)
% 3.85/0.98      | ~ l1_orders_2(sK6) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_581,plain,
% 3.85/0.98      ( r1_yellow_0(sK6,k1_xboole_0) ),
% 3.85/0.98      inference(global_propositional_subsumption,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_579,c_40,c_39,c_38,c_37,c_73]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_677,plain,
% 3.85/0.98      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.85/0.98      | ~ r2_lattice3(X0,X1,X2)
% 3.85/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.85/0.98      | ~ l1_orders_2(X0)
% 3.85/0.98      | sK6 != X0
% 3.85/0.98      | k1_xboole_0 != X1 ),
% 3.85/0.98      inference(resolution_lifted,[status(thm)],[c_253,c_581]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_678,plain,
% 3.85/0.98      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
% 3.85/0.98      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 3.85/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.85/0.98      | ~ l1_orders_2(sK6) ),
% 3.85/0.98      inference(unflattening,[status(thm)],[c_677]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_682,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.85/0.98      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 3.85/0.98      | r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) ),
% 3.85/0.98      inference(global_propositional_subsumption,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_678,c_37]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_683,plain,
% 3.85/0.98      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
% 3.85/0.98      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 3.85/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 3.85/0.98      inference(renaming,[status(thm)],[c_682]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2558,plain,
% 3.85/0.98      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) = iProver_top
% 3.85/0.98      | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 3.85/0.98      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_683]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_15,plain,
% 3.85/0.98      ( ~ l1_orders_2(X0)
% 3.85/0.98      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_834,plain,
% 3.85/0.98      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK6 != X0 ),
% 3.85/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_37]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_835,plain,
% 3.85/0.98      ( k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
% 3.85/0.98      inference(unflattening,[status(thm)],[c_834]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2663,plain,
% 3.85/0.98      ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
% 3.85/0.98      | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 3.85/0.98      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_2558,c_835]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4789,plain,
% 3.85/0.98      ( r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 3.85/0.98      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.85/0.98      | r2_hidden(X0,sK7) = iProver_top
% 3.85/0.98      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2663,c_4780]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_30,plain,
% 3.85/0.98      ( v1_subset_1(X0,X1)
% 3.85/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.85/0.98      | X0 = X1 ),
% 3.85/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_32,negated_conjecture,
% 3.85/0.98      ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
% 3.85/0.98      | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.85/0.98      inference(cnf_transformation,[],[f112]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_328,plain,
% 3.85/0.98      ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
% 3.85/0.98      | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.85/0.98      inference(prop_impl,[status(thm)],[c_32]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_615,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.85/0.98      | r2_hidden(k3_yellow_0(sK6),sK7)
% 3.85/0.98      | X1 = X0
% 3.85/0.98      | u1_struct_0(sK6) != X1
% 3.85/0.98      | sK7 != X0 ),
% 3.85/0.98      inference(resolution_lifted,[status(thm)],[c_30,c_328]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_616,plain,
% 3.85/0.98      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.85/0.98      | r2_hidden(k3_yellow_0(sK6),sK7)
% 3.85/0.98      | u1_struct_0(sK6) = sK7 ),
% 3.85/0.98      inference(unflattening,[status(thm)],[c_615]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_618,plain,
% 3.85/0.98      ( r2_hidden(k3_yellow_0(sK6),sK7) | u1_struct_0(sK6) = sK7 ),
% 3.85/0.98      inference(global_propositional_subsumption,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_616,c_34]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2561,plain,
% 3.85/0.98      ( u1_struct_0(sK6) = sK7
% 3.85/0.98      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_618]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_44,plain,
% 3.85/0.98      ( l1_orders_2(sK6) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_22,plain,
% 3.85/0.98      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 3.85/0.98      | ~ l1_orders_2(X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_75,plain,
% 3.85/0.98      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
% 3.85/0.98      | l1_orders_2(X0) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_77,plain,
% 3.85/0.98      ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top
% 3.85/0.98      | l1_orders_2(sK6) != iProver_top ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_75]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_617,plain,
% 3.85/0.98      ( u1_struct_0(sK6) = sK7
% 3.85/0.98      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.85/0.98      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2014,plain,
% 3.85/0.98      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 3.85/0.98      theory(equality) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2028,plain,
% 3.85/0.98      ( k3_yellow_0(sK6) = k3_yellow_0(sK6) | sK6 != sK6 ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_2014]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2004,plain,( X0 = X0 ),theory(equality) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2035,plain,
% 3.85/0.98      ( sK6 = sK6 ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_2004]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3041,plain,
% 3.85/0.98      ( sK7 = sK7 ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_2004]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2005,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3008,plain,
% 3.85/0.98      ( u1_struct_0(sK6) != X0 | sK7 != X0 | sK7 = u1_struct_0(sK6) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_2005]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3535,plain,
% 3.85/0.98      ( u1_struct_0(sK6) != sK7 | sK7 = u1_struct_0(sK6) | sK7 != sK7 ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_3008]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2008,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.85/0.98      theory(equality) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2953,plain,
% 3.85/0.98      ( m1_subset_1(X0,X1)
% 3.85/0.98      | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
% 3.85/0.98      | X0 != k3_yellow_0(sK6)
% 3.85/0.98      | X1 != u1_struct_0(sK6) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_2008]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3190,plain,
% 3.85/0.98      ( m1_subset_1(k3_yellow_0(sK6),X0)
% 3.85/0.98      | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
% 3.85/0.98      | X0 != u1_struct_0(sK6)
% 3.85/0.98      | k3_yellow_0(sK6) != k3_yellow_0(sK6) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_2953]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4198,plain,
% 3.85/0.98      ( ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
% 3.85/0.98      | m1_subset_1(k3_yellow_0(sK6),sK7)
% 3.85/0.98      | k3_yellow_0(sK6) != k3_yellow_0(sK6)
% 3.85/0.98      | sK7 != u1_struct_0(sK6) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_3190]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4199,plain,
% 3.85/0.98      ( k3_yellow_0(sK6) != k3_yellow_0(sK6)
% 3.85/0.98      | sK7 != u1_struct_0(sK6)
% 3.85/0.98      | m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top
% 3.85/0.98      | m1_subset_1(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_4198]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_8,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.85/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_36,negated_conjecture,
% 3.85/0.98      ( ~ v1_xboole_0(sK7) ),
% 3.85/0.98      inference(cnf_transformation,[],[f108]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_563,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK7 != X1 ),
% 3.85/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_36]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_564,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,sK7) | r2_hidden(X0,sK7) ),
% 3.85/0.98      inference(unflattening,[status(thm)],[c_563]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_5171,plain,
% 3.85/0.98      ( ~ m1_subset_1(k3_yellow_0(sK6),sK7)
% 3.85/0.98      | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_564]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_5172,plain,
% 3.85/0.98      ( m1_subset_1(k3_yellow_0(sK6),sK7) != iProver_top
% 3.85/0.98      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_5171]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_5419,plain,
% 3.85/0.98      ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.85/0.98      inference(global_propositional_subsumption,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_2561,c_44,c_47,c_77,c_617,c_2028,c_2035,c_3041,c_3535,
% 3.85/0.98                 c_4199,c_5172]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_12,plain,
% 3.85/0.98      ( r2_lattice3(X0,X1,X2)
% 3.85/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.85/0.98      | r2_hidden(sK2(X0,X1,X2),X1)
% 3.85/0.98      | ~ l1_orders_2(X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_875,plain,
% 3.85/0.98      ( r2_lattice3(X0,X1,X2)
% 3.85/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.85/0.98      | r2_hidden(sK2(X0,X1,X2),X1)
% 3.85/0.98      | sK6 != X0 ),
% 3.85/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_37]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_876,plain,
% 3.85/0.98      ( r2_lattice3(sK6,X0,X1)
% 3.85/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.85/0.98      | r2_hidden(sK2(sK6,X0,X1),X0) ),
% 3.85/0.98      inference(unflattening,[status(thm)],[c_875]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2548,plain,
% 3.85/0.98      ( r2_lattice3(sK6,X0,X1) = iProver_top
% 3.85/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.85/0.98      | r2_hidden(sK2(sK6,X0,X1),X0) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_876]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_0,plain,
% 3.85/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_10,plain,
% 3.85/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_552,plain,
% 3.85/0.98      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.85/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_10]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_553,plain,
% 3.85/0.98      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.85/0.98      inference(unflattening,[status(thm)],[c_552]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2564,plain,
% 3.85/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_553]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_6806,plain,
% 3.85/0.98      ( r2_lattice3(sK6,k1_xboole_0,X0) = iProver_top
% 3.85/0.98      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2548,c_2564]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_10731,plain,
% 3.85/0.98      ( r2_hidden(X0,sK7) = iProver_top
% 3.85/0.98      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.85/0.98      inference(global_propositional_subsumption,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_10695,c_44,c_47,c_77,c_617,c_2028,c_2035,c_3041,
% 3.85/0.98                 c_3535,c_4199,c_4789,c_5172,c_6806]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_10732,plain,
% 3.85/0.98      ( m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.85/0.98      | r2_hidden(X0,sK7) = iProver_top ),
% 3.85/0.98      inference(renaming,[status(thm)],[c_10731]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_10740,plain,
% 3.85/0.98      ( X0 = X1
% 3.85/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.85/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.85/0.98      | r2_hidden(sK0(u1_struct_0(sK6),X1,X0),sK7) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2570,c_10732]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.85/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.85/0.98      | ~ r2_hidden(sK0(X1,X0,X2),X2)
% 3.85/0.98      | ~ r2_hidden(sK0(X1,X0,X2),X0)
% 3.85/0.98      | X0 = X2 ),
% 3.85/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2572,plain,
% 3.85/0.98      ( X0 = X1
% 3.85/0.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.85/0.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.85/0.98      | r2_hidden(sK0(X2,X0,X1),X1) != iProver_top
% 3.85/0.98      | r2_hidden(sK0(X2,X0,X1),X0) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3877,plain,
% 3.85/0.98      ( u1_struct_0(sK6) = X0
% 3.85/0.98      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.85/0.98      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X1)) != iProver_top
% 3.85/0.98      | r2_hidden(sK0(X1,X0,u1_struct_0(sK6)),X0) != iProver_top
% 3.85/0.98      | r2_hidden(sK0(X1,X0,u1_struct_0(sK6)),sK7) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_3122,c_2572]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_11685,plain,
% 3.85/0.98      ( u1_struct_0(sK6) = sK7
% 3.85/0.98      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.85/0.98      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.85/0.98      | r2_hidden(sK0(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),sK7) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_10740,c_3877]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_11690,plain,
% 3.85/0.98      ( u1_struct_0(sK6) = sK7
% 3.85/0.98      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.85/0.98      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.85/0.98      inference(forward_subsumption_resolution,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_11685,c_10740]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2943,plain,
% 3.85/0.98      ( m1_subset_1(X0,X1)
% 3.85/0.98      | ~ m1_subset_1(sK1(X2),k1_zfmisc_1(X2))
% 3.85/0.98      | X0 != sK1(X2)
% 3.85/0.98      | X1 != k1_zfmisc_1(X2) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_2008]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3069,plain,
% 3.85/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.85/0.98      | ~ m1_subset_1(sK1(X1),k1_zfmisc_1(X1))
% 3.85/0.98      | X0 != sK1(X1)
% 3.85/0.98      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_2943]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3559,plain,
% 3.85/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.85/0.98      | ~ m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.85/0.98      | X0 != sK1(u1_struct_0(sK6))
% 3.85/0.98      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_3069]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_5851,plain,
% 3.85/0.98      ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.85/0.98      | ~ m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.85/0.98      | u1_struct_0(sK6) != sK1(u1_struct_0(sK6))
% 3.85/0.98      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_3559]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_5852,plain,
% 3.85/0.98      ( u1_struct_0(sK6) != sK1(u1_struct_0(sK6))
% 3.85/0.98      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
% 3.85/0.98      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 3.85/0.98      | m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_5851]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3070,plain,
% 3.85/0.98      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_2004]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3911,plain,
% 3.85/0.98      ( k1_zfmisc_1(u1_struct_0(sK6)) = k1_zfmisc_1(u1_struct_0(sK6)) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_3070]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_5,plain,
% 3.85/0.98      ( ~ v1_subset_1(sK1(X0),X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_592,plain,
% 3.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.85/0.98      | X1 != X2
% 3.85/0.98      | X1 = X0
% 3.85/0.98      | sK1(X2) != X0 ),
% 3.85/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_30]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_593,plain,
% 3.85/0.98      ( ~ m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) | X0 = sK1(X0) ),
% 3.85/0.98      inference(unflattening,[status(thm)],[c_592]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_6,plain,
% 3.85/0.98      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_597,plain,
% 3.85/0.98      ( X0 = sK1(X0) ),
% 3.85/0.98      inference(global_propositional_subsumption,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_593,c_6]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3453,plain,
% 3.85/0.98      ( u1_struct_0(sK6) = sK1(u1_struct_0(sK6)) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_597]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2902,plain,
% 3.85/0.98      ( m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2908,plain,
% 3.85/0.98      ( m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_2902]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_33,negated_conjecture,
% 3.85/0.98      ( v1_subset_1(sK7,u1_struct_0(sK6))
% 3.85/0.98      | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.85/0.98      inference(cnf_transformation,[],[f111]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_326,plain,
% 3.85/0.98      ( v1_subset_1(sK7,u1_struct_0(sK6))
% 3.85/0.98      | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.85/0.98      inference(prop_impl,[status(thm)],[c_33]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_603,plain,
% 3.85/0.98      ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 3.85/0.98      | u1_struct_0(sK6) != X0
% 3.85/0.98      | sK1(X0) != sK7 ),
% 3.85/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_326]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_604,plain,
% 3.85/0.98      ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 3.85/0.98      | sK1(u1_struct_0(sK6)) != sK7 ),
% 3.85/0.98      inference(unflattening,[status(thm)],[c_603]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2562,plain,
% 3.85/0.98      ( sK1(u1_struct_0(sK6)) != sK7
% 3.85/0.98      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_604]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2606,plain,
% 3.85/0.98      ( u1_struct_0(sK6) != sK7
% 3.85/0.98      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_2562,c_597]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(contradiction,plain,
% 3.85/0.98      ( $false ),
% 3.85/0.98      inference(minisat,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_11690,c_5852,c_5419,c_3911,c_3453,c_2908,c_2606,c_47]) ).
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  ------                               Statistics
% 3.85/0.98  
% 3.85/0.98  ------ General
% 3.85/0.98  
% 3.85/0.98  abstr_ref_over_cycles:                  0
% 3.85/0.98  abstr_ref_under_cycles:                 0
% 3.85/0.98  gc_basic_clause_elim:                   0
% 3.85/0.98  forced_gc_time:                         0
% 3.85/0.98  parsing_time:                           0.011
% 3.85/0.98  unif_index_cands_time:                  0.
% 3.85/0.98  unif_index_add_time:                    0.
% 3.85/0.98  orderings_time:                         0.
% 3.85/0.98  out_proof_time:                         0.013
% 3.85/0.98  total_time:                             0.336
% 3.85/0.98  num_of_symbols:                         57
% 3.85/0.98  num_of_terms:                           9006
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing
% 3.85/0.98  
% 3.85/0.98  num_of_splits:                          0
% 3.85/0.98  num_of_split_atoms:                     0
% 3.85/0.98  num_of_reused_defs:                     0
% 3.85/0.98  num_eq_ax_congr_red:                    36
% 3.85/0.98  num_of_sem_filtered_clauses:            1
% 3.85/0.98  num_of_subtypes:                        0
% 3.85/0.98  monotx_restored_types:                  0
% 3.85/0.98  sat_num_of_epr_types:                   0
% 3.85/0.98  sat_num_of_non_cyclic_types:            0
% 3.85/0.98  sat_guarded_non_collapsed_types:        0
% 3.85/0.98  num_pure_diseq_elim:                    0
% 3.85/0.98  simp_replaced_by:                       0
% 3.85/0.98  res_preprocessed:                       173
% 3.85/0.98  prep_upred:                             0
% 3.85/0.98  prep_unflattend:                        73
% 3.85/0.98  smt_new_axioms:                         0
% 3.85/0.98  pred_elim_cands:                        5
% 3.85/0.98  pred_elim:                              8
% 3.85/0.98  pred_elim_cl:                           8
% 3.85/0.98  pred_elim_cycles:                       12
% 3.85/0.98  merged_defs:                            2
% 3.85/0.98  merged_defs_ncl:                        0
% 3.85/0.98  bin_hyper_res:                          2
% 3.85/0.98  prep_cycles:                            4
% 3.85/0.98  pred_elim_time:                         0.024
% 3.85/0.98  splitting_time:                         0.
% 3.85/0.98  sem_filter_time:                        0.
% 3.85/0.98  monotx_time:                            0.
% 3.85/0.98  subtype_inf_time:                       0.
% 3.85/0.98  
% 3.85/0.98  ------ Problem properties
% 3.85/0.98  
% 3.85/0.98  clauses:                                33
% 3.85/0.98  conjectures:                            2
% 3.85/0.98  epr:                                    4
% 3.85/0.98  horn:                                   22
% 3.85/0.98  ground:                                 8
% 3.85/0.98  unary:                                  9
% 3.85/0.98  binary:                                 4
% 3.85/0.98  lits:                                   90
% 3.85/0.98  lits_eq:                                11
% 3.85/0.98  fd_pure:                                0
% 3.85/0.98  fd_pseudo:                              0
% 3.85/0.98  fd_cond:                                3
% 3.85/0.98  fd_pseudo_cond:                         3
% 3.85/0.98  ac_symbols:                             0
% 3.85/0.98  
% 3.85/0.98  ------ Propositional Solver
% 3.85/0.98  
% 3.85/0.98  prop_solver_calls:                      29
% 3.85/0.98  prop_fast_solver_calls:                 1699
% 3.85/0.98  smt_solver_calls:                       0
% 3.85/0.98  smt_fast_solver_calls:                  0
% 3.85/0.98  prop_num_of_clauses:                    3349
% 3.85/0.98  prop_preprocess_simplified:             8309
% 3.85/0.98  prop_fo_subsumed:                       32
% 3.85/0.98  prop_solver_time:                       0.
% 3.85/0.98  smt_solver_time:                        0.
% 3.85/0.98  smt_fast_solver_time:                   0.
% 3.85/0.98  prop_fast_solver_time:                  0.
% 3.85/0.98  prop_unsat_core_time:                   0.
% 3.85/0.98  
% 3.85/0.98  ------ QBF
% 3.85/0.98  
% 3.85/0.98  qbf_q_res:                              0
% 3.85/0.98  qbf_num_tautologies:                    0
% 3.85/0.98  qbf_prep_cycles:                        0
% 3.85/0.98  
% 3.85/0.98  ------ BMC1
% 3.85/0.98  
% 3.85/0.98  bmc1_current_bound:                     -1
% 3.85/0.98  bmc1_last_solved_bound:                 -1
% 3.85/0.98  bmc1_unsat_core_size:                   -1
% 3.85/0.98  bmc1_unsat_core_parents_size:           -1
% 3.85/0.98  bmc1_merge_next_fun:                    0
% 3.85/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.85/0.98  
% 3.85/0.98  ------ Instantiation
% 3.85/0.98  
% 3.85/0.98  inst_num_of_clauses:                    789
% 3.85/0.98  inst_num_in_passive:                    288
% 3.85/0.98  inst_num_in_active:                     440
% 3.85/0.98  inst_num_in_unprocessed:                61
% 3.85/0.98  inst_num_of_loops:                      510
% 3.85/0.98  inst_num_of_learning_restarts:          0
% 3.85/0.98  inst_num_moves_active_passive:          66
% 3.85/0.98  inst_lit_activity:                      0
% 3.85/0.98  inst_lit_activity_moves:                0
% 3.85/0.98  inst_num_tautologies:                   0
% 3.85/0.98  inst_num_prop_implied:                  0
% 3.85/0.98  inst_num_existing_simplified:           0
% 3.85/0.98  inst_num_eq_res_simplified:             0
% 3.85/0.98  inst_num_child_elim:                    0
% 3.85/0.98  inst_num_of_dismatching_blockings:      245
% 3.85/0.98  inst_num_of_non_proper_insts:           882
% 3.85/0.98  inst_num_of_duplicates:                 0
% 3.85/0.98  inst_inst_num_from_inst_to_res:         0
% 3.85/0.98  inst_dismatching_checking_time:         0.
% 3.85/0.98  
% 3.85/0.98  ------ Resolution
% 3.85/0.98  
% 3.85/0.98  res_num_of_clauses:                     0
% 3.85/0.98  res_num_in_passive:                     0
% 3.85/0.98  res_num_in_active:                      0
% 3.85/0.98  res_num_of_loops:                       177
% 3.85/0.98  res_forward_subset_subsumed:            151
% 3.85/0.98  res_backward_subset_subsumed:           0
% 3.85/0.98  res_forward_subsumed:                   0
% 3.85/0.98  res_backward_subsumed:                  0
% 3.85/0.98  res_forward_subsumption_resolution:     6
% 3.85/0.98  res_backward_subsumption_resolution:    0
% 3.85/0.98  res_clause_to_clause_subsumption:       2035
% 3.85/0.98  res_orphan_elimination:                 0
% 3.85/0.98  res_tautology_del:                      51
% 3.85/0.98  res_num_eq_res_simplified:              0
% 3.85/0.98  res_num_sel_changes:                    0
% 3.85/0.98  res_moves_from_active_to_pass:          0
% 3.85/0.98  
% 3.85/0.98  ------ Superposition
% 3.85/0.98  
% 3.85/0.98  sup_time_total:                         0.
% 3.85/0.98  sup_time_generating:                    0.
% 3.85/0.98  sup_time_sim_full:                      0.
% 3.85/0.98  sup_time_sim_immed:                     0.
% 3.85/0.98  
% 3.85/0.98  sup_num_of_clauses:                     287
% 3.85/0.98  sup_num_in_active:                      101
% 3.85/0.98  sup_num_in_passive:                     186
% 3.85/0.98  sup_num_of_loops:                       101
% 3.85/0.98  sup_fw_superposition:                   201
% 3.85/0.98  sup_bw_superposition:                   155
% 3.85/0.98  sup_immediate_simplified:               57
% 3.85/0.98  sup_given_eliminated:                   0
% 3.85/0.98  comparisons_done:                       0
% 3.85/0.98  comparisons_avoided:                    0
% 3.85/0.98  
% 3.85/0.98  ------ Simplifications
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  sim_fw_subset_subsumed:                 20
% 3.85/0.98  sim_bw_subset_subsumed:                 1
% 3.85/0.98  sim_fw_subsumed:                        19
% 3.85/0.98  sim_bw_subsumed:                        14
% 3.85/0.98  sim_fw_subsumption_res:                 3
% 3.85/0.98  sim_bw_subsumption_res:                 0
% 3.85/0.98  sim_tautology_del:                      7
% 3.85/0.98  sim_eq_tautology_del:                   16
% 3.85/0.98  sim_eq_res_simp:                        0
% 3.85/0.98  sim_fw_demodulated:                     4
% 3.85/0.98  sim_bw_demodulated:                     0
% 3.85/0.98  sim_light_normalised:                   6
% 3.85/0.98  sim_joinable_taut:                      0
% 3.85/0.98  sim_joinable_simp:                      0
% 3.85/0.98  sim_ac_normalised:                      0
% 3.85/0.98  sim_smt_subsumption:                    0
% 3.85/0.98  
%------------------------------------------------------------------------------
