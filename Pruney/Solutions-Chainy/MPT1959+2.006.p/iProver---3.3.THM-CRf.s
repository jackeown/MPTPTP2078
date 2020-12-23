%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:24 EST 2020

% Result     : Theorem 7.41s
% Output     : CNFRefutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :  287 (1741 expanded)
%              Number of clauses        :  178 ( 429 expanded)
%              Number of leaves         :   29 ( 329 expanded)
%              Depth                    :   25
%              Number of atoms          : 1172 (13410 expanded)
%              Number of equality atoms :  243 ( 495 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(nnf_transformation,[],[f38])).

fof(f63,plain,(
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
    inference(rectify,[],[f62])).

fof(f65,plain,(
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

fof(f64,plain,(
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

fof(f66,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f63,f65,f64])).

fof(f99,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
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
    inference(pure_predicate_removal,[],[f17])).

fof(f19,plain,(
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
    inference(pure_predicate_removal,[],[f18])).

fof(f20,plain,(
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
    inference(pure_predicate_removal,[],[f19])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

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
    inference(nnf_transformation,[],[f41])).

fof(f69,plain,(
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
    inference(flattening,[],[f68])).

fof(f71,plain,(
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

fof(f70,plain,
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

fof(f72,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f69,f71,f70])).

fof(f110,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f72])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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
    inference(nnf_transformation,[],[f33])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f59,plain,(
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
    inference(rectify,[],[f58])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f59,f60])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f118,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f98,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f109,plain,(
    v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f72])).

fof(f107,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f72])).

fof(f108,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f72])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f91,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f113,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f72])).

fof(f112,plain,(
    v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f72])).

fof(f111,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f72])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f105,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f120,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f105])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f117,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f115,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | ~ v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f72])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

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
    inference(flattening,[],[f23])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X2)
          | ~ r2_hidden(sK1(X0,X1,X2),X1) )
        & ( r2_hidden(sK1(X0,X1,X2),X2)
          | r2_hidden(sK1(X0,X1,X2),X1) )
        & m1_subset_1(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK1(X0,X1,X2),X2)
              | ~ r2_hidden(sK1(X0,X1,X2),X1) )
            & ( r2_hidden(sK1(X0,X1,X2),X2)
              | r2_hidden(sK1(X0,X1,X2),X1) )
            & m1_subset_1(sK1(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X2)
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | m1_subset_1(sK1(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f116,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f114,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f72])).

fof(f74,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_34963,plain,
    ( ~ r2_hidden(sK2(sK6,k1_xboole_0,sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6))),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_31,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_39,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_822,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_39])).

cnf(c_823,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(X2,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_822])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_839,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(X2,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_823,c_13])).

cnf(c_3360,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(sK7,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7) ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_10407,plain,
    ( ~ r1_orders_2(sK6,k1_yellow_0(sK6,X0),X1)
    | ~ v13_waybel_0(sK7,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(k1_yellow_0(sK6,X0),sK7) ),
    inference(instantiation,[status(thm)],[c_3360])).

cnf(c_13944,plain,
    ( ~ r1_orders_2(sK6,k1_yellow_0(sK6,X0),sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)))
    | ~ v13_waybel_0(sK7,sK6)
    | ~ m1_subset_1(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),sK7)
    | ~ r2_hidden(k1_yellow_0(sK6,X0),sK7) ),
    inference(instantiation,[status(thm)],[c_10407])).

cnf(c_31792,plain,
    ( ~ r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)))
    | ~ v13_waybel_0(sK7,sK6)
    | ~ m1_subset_1(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),sK7)
    | ~ r2_hidden(k1_yellow_0(sK6,k1_xboole_0),sK7) ),
    inference(instantiation,[status(thm)],[c_13944])).

cnf(c_15,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_912,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_39])).

cnf(c_913,plain,
    ( r2_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(sK2(sK6,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_912])).

cnf(c_7746,plain,
    ( r2_lattice3(sK6,X0,sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)))
    | ~ m1_subset_1(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
    | r2_hidden(sK2(sK6,X0,sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6))),X0) ),
    inference(instantiation,[status(thm)],[c_913])).

cnf(c_23760,plain,
    ( r2_lattice3(sK6,k1_xboole_0,sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)))
    | ~ m1_subset_1(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
    | r2_hidden(sK2(sK6,k1_xboole_0,sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6))),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7746])).

cnf(c_2194,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_7917,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | X0 != k3_yellow_0(sK6)
    | X1 != sK7 ),
    inference(instantiation,[status(thm)],[c_2194])).

cnf(c_13681,plain,
    ( r2_hidden(X0,sK7)
    | ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | X0 != k3_yellow_0(sK6)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_7917])).

cnf(c_22682,plain,
    ( r2_hidden(k1_yellow_0(sK6,k1_xboole_0),sK7)
    | ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | k1_yellow_0(sK6,k1_xboole_0) != k3_yellow_0(sK6)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_13681])).

cnf(c_22,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_24,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_24])).

cnf(c_260,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_259])).

cnf(c_25,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_40,negated_conjecture,
    ( v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_581,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_40])).

cnf(c_582,plain,
    ( r1_yellow_0(sK6,k1_xboole_0)
    | v2_struct_0(sK6)
    | ~ v5_orders_2(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_41,negated_conjecture,
    ( v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_75,plain,
    ( r1_yellow_0(sK6,k1_xboole_0)
    | v2_struct_0(sK6)
    | ~ v5_orders_2(sK6)
    | ~ v1_yellow_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_584,plain,
    ( r1_yellow_0(sK6,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_582,c_42,c_41,c_40,c_39,c_75])).

cnf(c_721,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK6 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_260,c_584])).

cnf(c_722,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
    | ~ r2_lattice3(sK6,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_721])).

cnf(c_726,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_lattice3(sK6,k1_xboole_0,X0)
    | r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_722,c_39])).

cnf(c_727,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
    | ~ r2_lattice3(sK6,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_726])).

cnf(c_14158,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)))
    | ~ r2_lattice3(sK6,k1_xboole_0,sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)))
    | ~ m1_subset_1(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_727])).

cnf(c_18,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_871,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_39])).

cnf(c_872,plain,
    ( k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
    inference(unflattening,[status(thm)],[c_871])).

cnf(c_862,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_39])).

cnf(c_863,plain,
    ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_862])).

cnf(c_3012,plain,
    ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_863])).

cnf(c_3386,plain,
    ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_872,c_3012])).

cnf(c_3009,plain,
    ( r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_913])).

cnf(c_16,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_897,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_39])).

cnf(c_898,plain,
    ( r2_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_897])).

cnf(c_3010,plain,
    ( r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_898])).

cnf(c_17,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_876,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_39])).

cnf(c_877,plain,
    ( r1_orders_2(sK6,X0,X1)
    | ~ r2_lattice3(sK6,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X0,X2) ),
    inference(unflattening,[status(thm)],[c_876])).

cnf(c_3011,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r2_lattice3(sK6,X2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_877])).

cnf(c_4673,plain,
    ( r1_orders_2(sK6,sK2(sK6,X0,X1),X2) = iProver_top
    | r2_lattice3(sK6,X3,X2) != iProver_top
    | r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0,X1),X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3010,c_3011])).

cnf(c_12004,plain,
    ( r1_orders_2(sK6,sK2(sK6,X0,X1),X2) = iProver_top
    | r2_lattice3(sK6,X0,X2) != iProver_top
    | r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3009,c_4673])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3025,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3014,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_839])).

cnf(c_5806,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3025,c_3014])).

cnf(c_37,negated_conjecture,
    ( v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1050,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK7 != X2
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_839])).

cnf(c_1051,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7) ),
    inference(unflattening,[status(thm)],[c_1050])).

cnf(c_1053,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r1_orders_2(sK6,X0,X1)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1051,c_36])).

cnf(c_1054,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7) ),
    inference(renaming,[status(thm)],[c_1053])).

cnf(c_1055,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1054])).

cnf(c_6089,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5806,c_1055])).

cnf(c_12121,plain,
    ( r2_lattice3(sK6,X0,X1) != iProver_top
    | r2_lattice3(sK6,X0,X2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top
    | r2_hidden(sK2(sK6,X0,X2),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_12004,c_6089])).

cnf(c_12160,plain,
    ( r2_lattice3(sK6,sK7,X0) != iProver_top
    | r2_lattice3(sK6,sK7,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3009,c_12121])).

cnf(c_38,negated_conjecture,
    ( ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_47,plain,
    ( v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_33,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_53,plain,
    ( ~ v1_subset_1(sK6,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_32,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_56,plain,
    ( v1_subset_1(sK6,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK6))
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_96,plain,
    ( ~ l1_orders_2(sK6)
    | k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_117,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK6))
    | ~ r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_133,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2202,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_2217,plain,
    ( k3_yellow_0(sK6) = k3_yellow_0(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2202])).

cnf(c_2191,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3489,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_2191])).

cnf(c_3817,plain,
    ( m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_3818,plain,
    ( m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3817])).

cnf(c_2192,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3449,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_2192])).

cnf(c_3698,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3449])).

cnf(c_4501,plain,
    ( u1_struct_0(sK6) != sK7
    | sK7 = u1_struct_0(sK6)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3698])).

cnf(c_3996,plain,
    ( X0 != X1
    | X0 = k1_yellow_0(sK6,X2)
    | k1_yellow_0(sK6,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_2192])).

cnf(c_5425,plain,
    ( X0 = k1_yellow_0(sK6,k1_xboole_0)
    | X0 != k3_yellow_0(sK6)
    | k1_yellow_0(sK6,k1_xboole_0) != k3_yellow_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3996])).

cnf(c_5873,plain,
    ( k1_yellow_0(sK6,k1_xboole_0) != k3_yellow_0(sK6)
    | k3_yellow_0(sK6) = k1_yellow_0(sK6,k1_xboole_0)
    | k3_yellow_0(sK6) != k3_yellow_0(sK6) ),
    inference(instantiation,[status(thm)],[c_5425])).

cnf(c_3018,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) = iProver_top
    | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_3140,plain,
    ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
    | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3018,c_872])).

cnf(c_6098,plain,
    ( r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3140,c_6089])).

cnf(c_23,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_252,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_24])).

cnf(c_253,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_252])).

cnf(c_742,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0)
    | sK6 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_253,c_584])).

cnf(c_743,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_742])).

cnf(c_745,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_743,c_39])).

cnf(c_3017,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_3049,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k3_yellow_0(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3017,c_872])).

cnf(c_3026,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5012,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3025,c_3026])).

cnf(c_5130,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r2_lattice3(sK6,X2,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5012,c_3011])).

cnf(c_6352,plain,
    ( r1_orders_2(sK6,X0,k3_yellow_0(sK6)) = iProver_top
    | r2_lattice3(sK6,X1,k3_yellow_0(sK6)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3386,c_5130])).

cnf(c_6572,plain,
    ( r1_orders_2(sK6,X0,k3_yellow_0(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3049,c_6352])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_625,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_626,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_627,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_6591,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6572,c_627])).

cnf(c_6599,plain,
    ( r2_lattice3(sK6,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3009,c_6591])).

cnf(c_2197,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3397,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(sK6,X2),u1_struct_0(sK6))
    | X0 != k1_yellow_0(sK6,X2)
    | X1 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2197])).

cnf(c_4958,plain,
    ( m1_subset_1(X0,sK7)
    | ~ m1_subset_1(k1_yellow_0(sK6,X1),u1_struct_0(sK6))
    | X0 != k1_yellow_0(sK6,X1)
    | sK7 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3397])).

cnf(c_6866,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),u1_struct_0(sK6))
    | m1_subset_1(k3_yellow_0(sK6),sK7)
    | k3_yellow_0(sK6) != k1_yellow_0(sK6,k1_xboole_0)
    | sK7 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4958])).

cnf(c_6870,plain,
    ( k3_yellow_0(sK6) != k1_yellow_0(sK6,k1_xboole_0)
    | sK7 != u1_struct_0(sK6)
    | m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6866])).

cnf(c_340,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_341,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_340])).

cnf(c_433,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_32,c_341])).

cnf(c_34,negated_conjecture,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_344,plain,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(prop_impl,[status(thm)],[c_34])).

cnf(c_663,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(k3_yellow_0(sK6),sK7)
    | X1 = X0
    | u1_struct_0(sK6) != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_433,c_344])).

cnf(c_664,plain,
    ( ~ r1_tarski(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(unflattening,[status(thm)],[c_663])).

cnf(c_3021,plain,
    ( u1_struct_0(sK6) = sK7
    | r1_tarski(sK7,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_49,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_665,plain,
    ( u1_struct_0(sK6) = sK7
    | r1_tarski(sK7,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3374,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r1_tarski(sK7,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3375,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3374])).

cnf(c_7840,plain,
    ( u1_struct_0(sK6) = sK7
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3021,c_49,c_665,c_3375])).

cnf(c_7848,plain,
    ( u1_struct_0(sK6) = sK7
    | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_7840,c_6098])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3388,plain,
    ( ~ m1_subset_1(X0,sK7)
    | r2_hidden(X0,sK7)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11452,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK6),sK7)
    | r2_hidden(k3_yellow_0(sK6),sK7)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3388])).

cnf(c_11453,plain,
    ( m1_subset_1(k3_yellow_0(sK6),sK7) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11452])).

cnf(c_12220,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12160,c_39,c_47,c_53,c_56,c_96,c_117,c_133,c_2217,c_3489,c_3818,c_4501,c_5873,c_6098,c_6599,c_6870,c_7848,c_11453])).

cnf(c_12235,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3386,c_12220])).

cnf(c_4976,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r2_hidden(X0,u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8590,plain,
    ( ~ m1_subset_1(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
    | r2_hidden(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_4976])).

cnf(c_7842,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7840])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X1,X0,X2),X2)
    | ~ r2_hidden(sK1(X1,X0,X2),X0)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(sK1(X1,X2,X0),X0)
    | ~ r2_hidden(sK1(X1,X2,X0),X2)
    | X2 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_341])).

cnf(c_1554,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_1555,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_1554])).

cnf(c_1622,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(sK1(X1,X2,X0),X0)
    | ~ r2_hidden(sK1(X1,X2,X0),X2)
    | X2 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_428,c_1555])).

cnf(c_3451,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(sK7,X1)
    | ~ r2_hidden(sK1(X1,sK7,X0),X0)
    | ~ r2_hidden(sK1(X1,sK7,X0),sK7)
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_1622])).

cnf(c_3799,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK6))
    | ~ r1_tarski(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(sK1(u1_struct_0(sK6),sK7,X0),X0)
    | ~ r2_hidden(sK1(u1_struct_0(sK6),sK7,X0),sK7)
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_3451])).

cnf(c_4816,plain,
    ( ~ r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6))
    | ~ r1_tarski(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
    | ~ r2_hidden(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),sK7)
    | sK7 = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3799])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK1(X1,X0,X2),X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK1(X1,X2,X0),X1)
    | ~ r1_tarski(X2,X1)
    | X2 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_341])).

cnf(c_1624,plain,
    ( m1_subset_1(sK1(X0,X1,X2),X0)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X1,X0)
    | X1 = X2 ),
    inference(bin_hyper_res,[status(thm)],[c_430,c_1555])).

cnf(c_3466,plain,
    ( m1_subset_1(sK1(X0,sK7,X1),X0)
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(sK7,X0)
    | sK7 = X1 ),
    inference(instantiation,[status(thm)],[c_1624])).

cnf(c_3785,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK6),sK7,X0),u1_struct_0(sK6))
    | ~ r1_tarski(X0,u1_struct_0(sK6))
    | ~ r1_tarski(sK7,u1_struct_0(sK6))
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_3466])).

cnf(c_4706,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
    | ~ r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6))
    | ~ r1_tarski(sK7,u1_struct_0(sK6))
    | sK7 = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3785])).

cnf(c_4364,plain,
    ( ~ r2_hidden(sK0(sK7),u1_struct_0(sK6))
    | ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_427,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_341])).

cnf(c_3439,plain,
    ( ~ r1_tarski(sK7,X0)
    | r2_hidden(sK0(sK7),X0)
    | ~ r2_hidden(sK0(sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_427])).

cnf(c_3786,plain,
    ( ~ r1_tarski(sK7,u1_struct_0(sK6))
    | r2_hidden(sK0(sK7),u1_struct_0(sK6))
    | ~ r2_hidden(sK0(sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_3439])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3508,plain,
    ( r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3511,plain,
    ( r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3508])).

cnf(c_3369,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_tarski(X0,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3507,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3369])).

cnf(c_3509,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3507])).

cnf(c_35,negated_conjecture,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_342,plain,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(prop_impl,[status(thm)],[c_35])).

cnf(c_676,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) != X0
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_342])).

cnf(c_677,plain,
    ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | sK7 != u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_678,plain,
    ( sK7 != u1_struct_0(sK6)
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_618,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_38])).

cnf(c_619,plain,
    ( r2_hidden(sK0(sK7),sK7) ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34963,c_31792,c_23760,c_22682,c_14158,c_12235,c_8590,c_7842,c_4816,c_4706,c_4501,c_4364,c_3786,c_3511,c_3508,c_3509,c_3489,c_3374,c_678,c_619,c_2,c_96,c_36,c_37,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:46:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 7.41/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.41/1.51  
% 7.41/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.41/1.51  
% 7.41/1.51  ------  iProver source info
% 7.41/1.51  
% 7.41/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.41/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.41/1.51  git: non_committed_changes: false
% 7.41/1.51  git: last_make_outside_of_git: false
% 7.41/1.51  
% 7.41/1.51  ------ 
% 7.41/1.51  
% 7.41/1.51  ------ Input Options
% 7.41/1.51  
% 7.41/1.51  --out_options                           all
% 7.41/1.51  --tptp_safe_out                         true
% 7.41/1.51  --problem_path                          ""
% 7.41/1.51  --include_path                          ""
% 7.41/1.51  --clausifier                            res/vclausify_rel
% 7.41/1.51  --clausifier_options                    --mode clausify
% 7.41/1.51  --stdin                                 false
% 7.41/1.51  --stats_out                             all
% 7.41/1.51  
% 7.41/1.51  ------ General Options
% 7.41/1.51  
% 7.41/1.51  --fof                                   false
% 7.41/1.51  --time_out_real                         305.
% 7.41/1.51  --time_out_virtual                      -1.
% 7.41/1.51  --symbol_type_check                     false
% 7.41/1.51  --clausify_out                          false
% 7.41/1.51  --sig_cnt_out                           false
% 7.41/1.51  --trig_cnt_out                          false
% 7.41/1.51  --trig_cnt_out_tolerance                1.
% 7.41/1.51  --trig_cnt_out_sk_spl                   false
% 7.41/1.51  --abstr_cl_out                          false
% 7.41/1.51  
% 7.41/1.51  ------ Global Options
% 7.41/1.51  
% 7.41/1.51  --schedule                              default
% 7.41/1.51  --add_important_lit                     false
% 7.41/1.51  --prop_solver_per_cl                    1000
% 7.41/1.51  --min_unsat_core                        false
% 7.41/1.51  --soft_assumptions                      false
% 7.41/1.51  --soft_lemma_size                       3
% 7.41/1.51  --prop_impl_unit_size                   0
% 7.41/1.51  --prop_impl_unit                        []
% 7.41/1.51  --share_sel_clauses                     true
% 7.41/1.51  --reset_solvers                         false
% 7.41/1.51  --bc_imp_inh                            [conj_cone]
% 7.41/1.51  --conj_cone_tolerance                   3.
% 7.41/1.51  --extra_neg_conj                        none
% 7.41/1.51  --large_theory_mode                     true
% 7.41/1.51  --prolific_symb_bound                   200
% 7.41/1.51  --lt_threshold                          2000
% 7.41/1.51  --clause_weak_htbl                      true
% 7.41/1.51  --gc_record_bc_elim                     false
% 7.41/1.51  
% 7.41/1.51  ------ Preprocessing Options
% 7.41/1.51  
% 7.41/1.51  --preprocessing_flag                    true
% 7.41/1.51  --time_out_prep_mult                    0.1
% 7.41/1.51  --splitting_mode                        input
% 7.41/1.51  --splitting_grd                         true
% 7.41/1.51  --splitting_cvd                         false
% 7.41/1.51  --splitting_cvd_svl                     false
% 7.41/1.51  --splitting_nvd                         32
% 7.41/1.51  --sub_typing                            true
% 7.41/1.51  --prep_gs_sim                           true
% 7.41/1.51  --prep_unflatten                        true
% 7.41/1.51  --prep_res_sim                          true
% 7.41/1.51  --prep_upred                            true
% 7.41/1.51  --prep_sem_filter                       exhaustive
% 7.41/1.51  --prep_sem_filter_out                   false
% 7.41/1.51  --pred_elim                             true
% 7.41/1.51  --res_sim_input                         true
% 7.41/1.51  --eq_ax_congr_red                       true
% 7.41/1.51  --pure_diseq_elim                       true
% 7.41/1.51  --brand_transform                       false
% 7.41/1.51  --non_eq_to_eq                          false
% 7.41/1.51  --prep_def_merge                        true
% 7.41/1.51  --prep_def_merge_prop_impl              false
% 7.41/1.51  --prep_def_merge_mbd                    true
% 7.41/1.51  --prep_def_merge_tr_red                 false
% 7.41/1.51  --prep_def_merge_tr_cl                  false
% 7.41/1.51  --smt_preprocessing                     true
% 7.41/1.51  --smt_ac_axioms                         fast
% 7.41/1.51  --preprocessed_out                      false
% 7.41/1.51  --preprocessed_stats                    false
% 7.41/1.51  
% 7.41/1.51  ------ Abstraction refinement Options
% 7.41/1.51  
% 7.41/1.51  --abstr_ref                             []
% 7.41/1.51  --abstr_ref_prep                        false
% 7.41/1.51  --abstr_ref_until_sat                   false
% 7.41/1.51  --abstr_ref_sig_restrict                funpre
% 7.41/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.41/1.51  --abstr_ref_under                       []
% 7.41/1.51  
% 7.41/1.51  ------ SAT Options
% 7.41/1.51  
% 7.41/1.51  --sat_mode                              false
% 7.41/1.51  --sat_fm_restart_options                ""
% 7.41/1.51  --sat_gr_def                            false
% 7.41/1.51  --sat_epr_types                         true
% 7.41/1.51  --sat_non_cyclic_types                  false
% 7.41/1.51  --sat_finite_models                     false
% 7.41/1.51  --sat_fm_lemmas                         false
% 7.41/1.51  --sat_fm_prep                           false
% 7.41/1.51  --sat_fm_uc_incr                        true
% 7.41/1.51  --sat_out_model                         small
% 7.41/1.51  --sat_out_clauses                       false
% 7.41/1.51  
% 7.41/1.51  ------ QBF Options
% 7.41/1.51  
% 7.41/1.51  --qbf_mode                              false
% 7.41/1.51  --qbf_elim_univ                         false
% 7.41/1.51  --qbf_dom_inst                          none
% 7.41/1.51  --qbf_dom_pre_inst                      false
% 7.41/1.51  --qbf_sk_in                             false
% 7.41/1.51  --qbf_pred_elim                         true
% 7.41/1.51  --qbf_split                             512
% 7.41/1.51  
% 7.41/1.51  ------ BMC1 Options
% 7.41/1.51  
% 7.41/1.51  --bmc1_incremental                      false
% 7.41/1.51  --bmc1_axioms                           reachable_all
% 7.41/1.51  --bmc1_min_bound                        0
% 7.41/1.51  --bmc1_max_bound                        -1
% 7.41/1.51  --bmc1_max_bound_default                -1
% 7.41/1.51  --bmc1_symbol_reachability              true
% 7.41/1.51  --bmc1_property_lemmas                  false
% 7.41/1.51  --bmc1_k_induction                      false
% 7.41/1.51  --bmc1_non_equiv_states                 false
% 7.41/1.51  --bmc1_deadlock                         false
% 7.41/1.51  --bmc1_ucm                              false
% 7.41/1.51  --bmc1_add_unsat_core                   none
% 7.41/1.51  --bmc1_unsat_core_children              false
% 7.41/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.41/1.51  --bmc1_out_stat                         full
% 7.41/1.51  --bmc1_ground_init                      false
% 7.41/1.51  --bmc1_pre_inst_next_state              false
% 7.41/1.51  --bmc1_pre_inst_state                   false
% 7.41/1.51  --bmc1_pre_inst_reach_state             false
% 7.41/1.51  --bmc1_out_unsat_core                   false
% 7.41/1.51  --bmc1_aig_witness_out                  false
% 7.41/1.51  --bmc1_verbose                          false
% 7.41/1.51  --bmc1_dump_clauses_tptp                false
% 7.41/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.41/1.51  --bmc1_dump_file                        -
% 7.41/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.41/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.41/1.51  --bmc1_ucm_extend_mode                  1
% 7.41/1.51  --bmc1_ucm_init_mode                    2
% 7.41/1.51  --bmc1_ucm_cone_mode                    none
% 7.41/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.41/1.51  --bmc1_ucm_relax_model                  4
% 7.41/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.41/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.41/1.51  --bmc1_ucm_layered_model                none
% 7.41/1.51  --bmc1_ucm_max_lemma_size               10
% 7.41/1.51  
% 7.41/1.51  ------ AIG Options
% 7.41/1.51  
% 7.41/1.51  --aig_mode                              false
% 7.41/1.51  
% 7.41/1.51  ------ Instantiation Options
% 7.41/1.51  
% 7.41/1.51  --instantiation_flag                    true
% 7.41/1.51  --inst_sos_flag                         false
% 7.41/1.51  --inst_sos_phase                        true
% 7.41/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.41/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.41/1.51  --inst_lit_sel_side                     num_symb
% 7.41/1.51  --inst_solver_per_active                1400
% 7.41/1.51  --inst_solver_calls_frac                1.
% 7.41/1.51  --inst_passive_queue_type               priority_queues
% 7.41/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.41/1.51  --inst_passive_queues_freq              [25;2]
% 7.41/1.51  --inst_dismatching                      true
% 7.41/1.51  --inst_eager_unprocessed_to_passive     true
% 7.41/1.51  --inst_prop_sim_given                   true
% 7.41/1.51  --inst_prop_sim_new                     false
% 7.41/1.51  --inst_subs_new                         false
% 7.41/1.51  --inst_eq_res_simp                      false
% 7.41/1.51  --inst_subs_given                       false
% 7.41/1.51  --inst_orphan_elimination               true
% 7.41/1.51  --inst_learning_loop_flag               true
% 7.41/1.51  --inst_learning_start                   3000
% 7.41/1.51  --inst_learning_factor                  2
% 7.41/1.51  --inst_start_prop_sim_after_learn       3
% 7.41/1.51  --inst_sel_renew                        solver
% 7.41/1.51  --inst_lit_activity_flag                true
% 7.41/1.51  --inst_restr_to_given                   false
% 7.41/1.51  --inst_activity_threshold               500
% 7.41/1.51  --inst_out_proof                        true
% 7.41/1.51  
% 7.41/1.51  ------ Resolution Options
% 7.41/1.51  
% 7.41/1.51  --resolution_flag                       true
% 7.41/1.51  --res_lit_sel                           adaptive
% 7.41/1.51  --res_lit_sel_side                      none
% 7.41/1.51  --res_ordering                          kbo
% 7.41/1.51  --res_to_prop_solver                    active
% 7.41/1.51  --res_prop_simpl_new                    false
% 7.41/1.51  --res_prop_simpl_given                  true
% 7.41/1.51  --res_passive_queue_type                priority_queues
% 7.41/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.41/1.51  --res_passive_queues_freq               [15;5]
% 7.41/1.51  --res_forward_subs                      full
% 7.41/1.51  --res_backward_subs                     full
% 7.41/1.51  --res_forward_subs_resolution           true
% 7.41/1.51  --res_backward_subs_resolution          true
% 7.41/1.51  --res_orphan_elimination                true
% 7.41/1.51  --res_time_limit                        2.
% 7.41/1.51  --res_out_proof                         true
% 7.41/1.51  
% 7.41/1.51  ------ Superposition Options
% 7.41/1.51  
% 7.41/1.51  --superposition_flag                    true
% 7.41/1.51  --sup_passive_queue_type                priority_queues
% 7.41/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.41/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.41/1.51  --demod_completeness_check              fast
% 7.41/1.51  --demod_use_ground                      true
% 7.41/1.51  --sup_to_prop_solver                    passive
% 7.41/1.51  --sup_prop_simpl_new                    true
% 7.41/1.51  --sup_prop_simpl_given                  true
% 7.41/1.51  --sup_fun_splitting                     false
% 7.41/1.51  --sup_smt_interval                      50000
% 7.41/1.51  
% 7.41/1.51  ------ Superposition Simplification Setup
% 7.41/1.51  
% 7.41/1.51  --sup_indices_passive                   []
% 7.41/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.41/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.41/1.51  --sup_full_bw                           [BwDemod]
% 7.41/1.51  --sup_immed_triv                        [TrivRules]
% 7.41/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.41/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.41/1.51  --sup_immed_bw_main                     []
% 7.41/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.41/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.41/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.41/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.41/1.51  
% 7.41/1.51  ------ Combination Options
% 7.41/1.51  
% 7.41/1.51  --comb_res_mult                         3
% 7.41/1.51  --comb_sup_mult                         2
% 7.41/1.51  --comb_inst_mult                        10
% 7.41/1.51  
% 7.41/1.51  ------ Debug Options
% 7.41/1.51  
% 7.41/1.51  --dbg_backtrace                         false
% 7.41/1.51  --dbg_dump_prop_clauses                 false
% 7.41/1.51  --dbg_dump_prop_clauses_file            -
% 7.41/1.51  --dbg_out_stat                          false
% 7.41/1.51  ------ Parsing...
% 7.41/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.41/1.51  
% 7.41/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 7.41/1.51  
% 7.41/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.41/1.51  
% 7.41/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.41/1.51  ------ Proving...
% 7.41/1.51  ------ Problem Properties 
% 7.41/1.51  
% 7.41/1.51  
% 7.41/1.51  clauses                                 35
% 7.41/1.51  conjectures                             3
% 7.41/1.51  EPR                                     8
% 7.41/1.51  Horn                                    22
% 7.41/1.51  unary                                   8
% 7.41/1.51  binary                                  4
% 7.41/1.51  lits                                    98
% 7.41/1.51  lits eq                                 10
% 7.41/1.51  fd_pure                                 0
% 7.41/1.51  fd_pseudo                               0
% 7.41/1.51  fd_cond                                 3
% 7.41/1.51  fd_pseudo_cond                          4
% 7.41/1.51  AC symbols                              0
% 7.41/1.51  
% 7.41/1.51  ------ Schedule dynamic 5 is on 
% 7.41/1.51  
% 7.41/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.41/1.51  
% 7.41/1.51  
% 7.41/1.51  ------ 
% 7.41/1.51  Current options:
% 7.41/1.51  ------ 
% 7.41/1.51  
% 7.41/1.51  ------ Input Options
% 7.41/1.51  
% 7.41/1.51  --out_options                           all
% 7.41/1.51  --tptp_safe_out                         true
% 7.41/1.51  --problem_path                          ""
% 7.41/1.51  --include_path                          ""
% 7.41/1.51  --clausifier                            res/vclausify_rel
% 7.41/1.51  --clausifier_options                    --mode clausify
% 7.41/1.51  --stdin                                 false
% 7.41/1.51  --stats_out                             all
% 7.41/1.52  
% 7.41/1.52  ------ General Options
% 7.41/1.52  
% 7.41/1.52  --fof                                   false
% 7.41/1.52  --time_out_real                         305.
% 7.41/1.52  --time_out_virtual                      -1.
% 7.41/1.52  --symbol_type_check                     false
% 7.41/1.52  --clausify_out                          false
% 7.41/1.52  --sig_cnt_out                           false
% 7.41/1.52  --trig_cnt_out                          false
% 7.41/1.52  --trig_cnt_out_tolerance                1.
% 7.41/1.52  --trig_cnt_out_sk_spl                   false
% 7.41/1.52  --abstr_cl_out                          false
% 7.41/1.52  
% 7.41/1.52  ------ Global Options
% 7.41/1.52  
% 7.41/1.52  --schedule                              default
% 7.41/1.52  --add_important_lit                     false
% 7.41/1.52  --prop_solver_per_cl                    1000
% 7.41/1.52  --min_unsat_core                        false
% 7.41/1.52  --soft_assumptions                      false
% 7.41/1.52  --soft_lemma_size                       3
% 7.41/1.52  --prop_impl_unit_size                   0
% 7.41/1.52  --prop_impl_unit                        []
% 7.41/1.52  --share_sel_clauses                     true
% 7.41/1.52  --reset_solvers                         false
% 7.41/1.52  --bc_imp_inh                            [conj_cone]
% 7.41/1.52  --conj_cone_tolerance                   3.
% 7.41/1.52  --extra_neg_conj                        none
% 7.41/1.52  --large_theory_mode                     true
% 7.41/1.52  --prolific_symb_bound                   200
% 7.41/1.52  --lt_threshold                          2000
% 7.41/1.52  --clause_weak_htbl                      true
% 7.41/1.52  --gc_record_bc_elim                     false
% 7.41/1.52  
% 7.41/1.52  ------ Preprocessing Options
% 7.41/1.52  
% 7.41/1.52  --preprocessing_flag                    true
% 7.41/1.52  --time_out_prep_mult                    0.1
% 7.41/1.52  --splitting_mode                        input
% 7.41/1.52  --splitting_grd                         true
% 7.41/1.52  --splitting_cvd                         false
% 7.41/1.52  --splitting_cvd_svl                     false
% 7.41/1.52  --splitting_nvd                         32
% 7.41/1.52  --sub_typing                            true
% 7.41/1.52  --prep_gs_sim                           true
% 7.41/1.52  --prep_unflatten                        true
% 7.41/1.52  --prep_res_sim                          true
% 7.41/1.52  --prep_upred                            true
% 7.41/1.52  --prep_sem_filter                       exhaustive
% 7.41/1.52  --prep_sem_filter_out                   false
% 7.41/1.52  --pred_elim                             true
% 7.41/1.52  --res_sim_input                         true
% 7.41/1.52  --eq_ax_congr_red                       true
% 7.41/1.52  --pure_diseq_elim                       true
% 7.41/1.52  --brand_transform                       false
% 7.41/1.52  --non_eq_to_eq                          false
% 7.41/1.52  --prep_def_merge                        true
% 7.41/1.52  --prep_def_merge_prop_impl              false
% 7.41/1.52  --prep_def_merge_mbd                    true
% 7.41/1.52  --prep_def_merge_tr_red                 false
% 7.41/1.52  --prep_def_merge_tr_cl                  false
% 7.41/1.52  --smt_preprocessing                     true
% 7.41/1.52  --smt_ac_axioms                         fast
% 7.41/1.52  --preprocessed_out                      false
% 7.41/1.52  --preprocessed_stats                    false
% 7.41/1.52  
% 7.41/1.52  ------ Abstraction refinement Options
% 7.41/1.52  
% 7.41/1.52  --abstr_ref                             []
% 7.41/1.52  --abstr_ref_prep                        false
% 7.41/1.52  --abstr_ref_until_sat                   false
% 7.41/1.52  --abstr_ref_sig_restrict                funpre
% 7.41/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.41/1.52  --abstr_ref_under                       []
% 7.41/1.52  
% 7.41/1.52  ------ SAT Options
% 7.41/1.52  
% 7.41/1.52  --sat_mode                              false
% 7.41/1.52  --sat_fm_restart_options                ""
% 7.41/1.52  --sat_gr_def                            false
% 7.41/1.52  --sat_epr_types                         true
% 7.41/1.52  --sat_non_cyclic_types                  false
% 7.41/1.52  --sat_finite_models                     false
% 7.41/1.52  --sat_fm_lemmas                         false
% 7.41/1.52  --sat_fm_prep                           false
% 7.41/1.52  --sat_fm_uc_incr                        true
% 7.41/1.52  --sat_out_model                         small
% 7.41/1.52  --sat_out_clauses                       false
% 7.41/1.52  
% 7.41/1.52  ------ QBF Options
% 7.41/1.52  
% 7.41/1.52  --qbf_mode                              false
% 7.41/1.52  --qbf_elim_univ                         false
% 7.41/1.52  --qbf_dom_inst                          none
% 7.41/1.52  --qbf_dom_pre_inst                      false
% 7.41/1.52  --qbf_sk_in                             false
% 7.41/1.52  --qbf_pred_elim                         true
% 7.41/1.52  --qbf_split                             512
% 7.41/1.52  
% 7.41/1.52  ------ BMC1 Options
% 7.41/1.52  
% 7.41/1.52  --bmc1_incremental                      false
% 7.41/1.52  --bmc1_axioms                           reachable_all
% 7.41/1.52  --bmc1_min_bound                        0
% 7.41/1.52  --bmc1_max_bound                        -1
% 7.41/1.52  --bmc1_max_bound_default                -1
% 7.41/1.52  --bmc1_symbol_reachability              true
% 7.41/1.52  --bmc1_property_lemmas                  false
% 7.41/1.52  --bmc1_k_induction                      false
% 7.41/1.52  --bmc1_non_equiv_states                 false
% 7.41/1.52  --bmc1_deadlock                         false
% 7.41/1.52  --bmc1_ucm                              false
% 7.41/1.52  --bmc1_add_unsat_core                   none
% 7.41/1.52  --bmc1_unsat_core_children              false
% 7.41/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.41/1.52  --bmc1_out_stat                         full
% 7.41/1.52  --bmc1_ground_init                      false
% 7.41/1.52  --bmc1_pre_inst_next_state              false
% 7.41/1.52  --bmc1_pre_inst_state                   false
% 7.41/1.52  --bmc1_pre_inst_reach_state             false
% 7.41/1.52  --bmc1_out_unsat_core                   false
% 7.41/1.52  --bmc1_aig_witness_out                  false
% 7.41/1.52  --bmc1_verbose                          false
% 7.41/1.52  --bmc1_dump_clauses_tptp                false
% 7.41/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.41/1.52  --bmc1_dump_file                        -
% 7.41/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.41/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.41/1.52  --bmc1_ucm_extend_mode                  1
% 7.41/1.52  --bmc1_ucm_init_mode                    2
% 7.41/1.52  --bmc1_ucm_cone_mode                    none
% 7.41/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.41/1.52  --bmc1_ucm_relax_model                  4
% 7.41/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.41/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.41/1.52  --bmc1_ucm_layered_model                none
% 7.41/1.52  --bmc1_ucm_max_lemma_size               10
% 7.41/1.52  
% 7.41/1.52  ------ AIG Options
% 7.41/1.52  
% 7.41/1.52  --aig_mode                              false
% 7.41/1.52  
% 7.41/1.52  ------ Instantiation Options
% 7.41/1.52  
% 7.41/1.52  --instantiation_flag                    true
% 7.41/1.52  --inst_sos_flag                         false
% 7.41/1.52  --inst_sos_phase                        true
% 7.41/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.41/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.41/1.52  --inst_lit_sel_side                     none
% 7.41/1.52  --inst_solver_per_active                1400
% 7.41/1.52  --inst_solver_calls_frac                1.
% 7.41/1.52  --inst_passive_queue_type               priority_queues
% 7.41/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.41/1.52  --inst_passive_queues_freq              [25;2]
% 7.41/1.52  --inst_dismatching                      true
% 7.41/1.52  --inst_eager_unprocessed_to_passive     true
% 7.41/1.52  --inst_prop_sim_given                   true
% 7.41/1.52  --inst_prop_sim_new                     false
% 7.41/1.52  --inst_subs_new                         false
% 7.41/1.52  --inst_eq_res_simp                      false
% 7.41/1.52  --inst_subs_given                       false
% 7.41/1.52  --inst_orphan_elimination               true
% 7.41/1.52  --inst_learning_loop_flag               true
% 7.41/1.52  --inst_learning_start                   3000
% 7.41/1.52  --inst_learning_factor                  2
% 7.41/1.52  --inst_start_prop_sim_after_learn       3
% 7.41/1.52  --inst_sel_renew                        solver
% 7.41/1.52  --inst_lit_activity_flag                true
% 7.41/1.52  --inst_restr_to_given                   false
% 7.41/1.52  --inst_activity_threshold               500
% 7.41/1.52  --inst_out_proof                        true
% 7.41/1.52  
% 7.41/1.52  ------ Resolution Options
% 7.41/1.52  
% 7.41/1.52  --resolution_flag                       false
% 7.41/1.52  --res_lit_sel                           adaptive
% 7.41/1.52  --res_lit_sel_side                      none
% 7.41/1.52  --res_ordering                          kbo
% 7.41/1.52  --res_to_prop_solver                    active
% 7.41/1.52  --res_prop_simpl_new                    false
% 7.41/1.52  --res_prop_simpl_given                  true
% 7.41/1.52  --res_passive_queue_type                priority_queues
% 7.41/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.41/1.52  --res_passive_queues_freq               [15;5]
% 7.41/1.52  --res_forward_subs                      full
% 7.41/1.52  --res_backward_subs                     full
% 7.41/1.52  --res_forward_subs_resolution           true
% 7.41/1.52  --res_backward_subs_resolution          true
% 7.41/1.52  --res_orphan_elimination                true
% 7.41/1.52  --res_time_limit                        2.
% 7.41/1.52  --res_out_proof                         true
% 7.41/1.52  
% 7.41/1.52  ------ Superposition Options
% 7.41/1.52  
% 7.41/1.52  --superposition_flag                    true
% 7.41/1.52  --sup_passive_queue_type                priority_queues
% 7.41/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.41/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.41/1.52  --demod_completeness_check              fast
% 7.41/1.52  --demod_use_ground                      true
% 7.41/1.52  --sup_to_prop_solver                    passive
% 7.41/1.52  --sup_prop_simpl_new                    true
% 7.41/1.52  --sup_prop_simpl_given                  true
% 7.41/1.52  --sup_fun_splitting                     false
% 7.41/1.52  --sup_smt_interval                      50000
% 7.41/1.52  
% 7.41/1.52  ------ Superposition Simplification Setup
% 7.41/1.52  
% 7.41/1.52  --sup_indices_passive                   []
% 7.41/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.41/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.41/1.52  --sup_full_bw                           [BwDemod]
% 7.41/1.52  --sup_immed_triv                        [TrivRules]
% 7.41/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.41/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.41/1.52  --sup_immed_bw_main                     []
% 7.41/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.41/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.41/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.41/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.41/1.52  
% 7.41/1.52  ------ Combination Options
% 7.41/1.52  
% 7.41/1.52  --comb_res_mult                         3
% 7.41/1.52  --comb_sup_mult                         2
% 7.41/1.52  --comb_inst_mult                        10
% 7.41/1.52  
% 7.41/1.52  ------ Debug Options
% 7.41/1.52  
% 7.41/1.52  --dbg_backtrace                         false
% 7.41/1.52  --dbg_dump_prop_clauses                 false
% 7.41/1.52  --dbg_dump_prop_clauses_file            -
% 7.41/1.52  --dbg_out_stat                          false
% 7.41/1.52  
% 7.41/1.52  
% 7.41/1.52  
% 7.41/1.52  
% 7.41/1.52  ------ Proving...
% 7.41/1.52  
% 7.41/1.52  
% 7.41/1.52  % SZS status Theorem for theBenchmark.p
% 7.41/1.52  
% 7.41/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.41/1.52  
% 7.41/1.52  fof(f1,axiom,(
% 7.41/1.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.52  
% 7.41/1.52  fof(f42,plain,(
% 7.41/1.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.41/1.52    inference(nnf_transformation,[],[f1])).
% 7.41/1.52  
% 7.41/1.52  fof(f43,plain,(
% 7.41/1.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.41/1.52    inference(rectify,[],[f42])).
% 7.41/1.52  
% 7.41/1.52  fof(f44,plain,(
% 7.41/1.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.41/1.52    introduced(choice_axiom,[])).
% 7.41/1.52  
% 7.41/1.52  fof(f45,plain,(
% 7.41/1.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.41/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 7.41/1.52  
% 7.41/1.52  fof(f73,plain,(
% 7.41/1.52    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.41/1.52    inference(cnf_transformation,[],[f45])).
% 7.41/1.52  
% 7.41/1.52  fof(f14,axiom,(
% 7.41/1.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 7.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.52  
% 7.41/1.52  fof(f37,plain,(
% 7.41/1.52    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.41/1.52    inference(ennf_transformation,[],[f14])).
% 7.41/1.52  
% 7.41/1.52  fof(f38,plain,(
% 7.41/1.52    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.41/1.52    inference(flattening,[],[f37])).
% 7.41/1.52  
% 7.41/1.52  fof(f62,plain,(
% 7.41/1.52    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.41/1.52    inference(nnf_transformation,[],[f38])).
% 7.41/1.52  
% 7.41/1.52  fof(f63,plain,(
% 7.41/1.52    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.41/1.52    inference(rectify,[],[f62])).
% 7.41/1.52  
% 7.41/1.52  fof(f65,plain,(
% 7.41/1.52    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,X2,sK5(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))) )),
% 7.41/1.52    introduced(choice_axiom,[])).
% 7.41/1.52  
% 7.41/1.52  fof(f64,plain,(
% 7.41/1.52    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 7.41/1.52    introduced(choice_axiom,[])).
% 7.41/1.52  
% 7.41/1.52  fof(f66,plain,(
% 7.41/1.52    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.41/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f63,f65,f64])).
% 7.41/1.52  
% 7.41/1.52  fof(f99,plain,(
% 7.41/1.52    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 7.41/1.52    inference(cnf_transformation,[],[f66])).
% 7.41/1.52  
% 7.41/1.52  fof(f16,conjecture,(
% 7.41/1.52    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.52  
% 7.41/1.52  fof(f17,negated_conjecture,(
% 7.41/1.52    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.41/1.52    inference(negated_conjecture,[],[f16])).
% 7.41/1.52  
% 7.41/1.52  fof(f18,plain,(
% 7.41/1.52    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.41/1.52    inference(pure_predicate_removal,[],[f17])).
% 7.41/1.52  
% 7.41/1.52  fof(f19,plain,(
% 7.41/1.52    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.41/1.52    inference(pure_predicate_removal,[],[f18])).
% 7.41/1.52  
% 7.41/1.52  fof(f20,plain,(
% 7.41/1.52    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.41/1.52    inference(pure_predicate_removal,[],[f19])).
% 7.41/1.52  
% 7.41/1.52  fof(f40,plain,(
% 7.41/1.52    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 7.41/1.52    inference(ennf_transformation,[],[f20])).
% 7.41/1.52  
% 7.41/1.52  fof(f41,plain,(
% 7.41/1.52    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 7.41/1.52    inference(flattening,[],[f40])).
% 7.41/1.52  
% 7.41/1.52  fof(f68,plain,(
% 7.41/1.52    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 7.41/1.52    inference(nnf_transformation,[],[f41])).
% 7.41/1.52  
% 7.41/1.52  fof(f69,plain,(
% 7.41/1.52    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 7.41/1.52    inference(flattening,[],[f68])).
% 7.41/1.52  
% 7.41/1.52  fof(f71,plain,(
% 7.41/1.52    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK7) | ~v1_subset_1(sK7,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK7) | v1_subset_1(sK7,u1_struct_0(X0))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK7,X0) & ~v1_xboole_0(sK7))) )),
% 7.41/1.52    introduced(choice_axiom,[])).
% 7.41/1.52  
% 7.41/1.52  fof(f70,plain,(
% 7.41/1.52    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK6),X1) | ~v1_subset_1(X1,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),X1) | v1_subset_1(X1,u1_struct_0(sK6))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(X1,sK6) & ~v1_xboole_0(X1)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & ~v2_struct_0(sK6))),
% 7.41/1.52    introduced(choice_axiom,[])).
% 7.41/1.52  
% 7.41/1.52  fof(f72,plain,(
% 7.41/1.52    ((r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(sK7,sK6) & ~v1_xboole_0(sK7)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & ~v2_struct_0(sK6)),
% 7.41/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f69,f71,f70])).
% 7.41/1.52  
% 7.41/1.52  fof(f110,plain,(
% 7.41/1.52    l1_orders_2(sK6)),
% 7.41/1.52    inference(cnf_transformation,[],[f72])).
% 7.41/1.52  
% 7.41/1.52  fof(f8,axiom,(
% 7.41/1.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.52  
% 7.41/1.52  fof(f27,plain,(
% 7.41/1.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.41/1.52    inference(ennf_transformation,[],[f8])).
% 7.41/1.52  
% 7.41/1.52  fof(f28,plain,(
% 7.41/1.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.41/1.52    inference(flattening,[],[f27])).
% 7.41/1.52  
% 7.41/1.52  fof(f86,plain,(
% 7.41/1.52    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.41/1.52    inference(cnf_transformation,[],[f28])).
% 7.41/1.52  
% 7.41/1.52  fof(f9,axiom,(
% 7.41/1.52    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 7.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.52  
% 7.41/1.52  fof(f29,plain,(
% 7.41/1.52    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.41/1.52    inference(ennf_transformation,[],[f9])).
% 7.41/1.52  
% 7.41/1.52  fof(f30,plain,(
% 7.41/1.52    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.41/1.52    inference(flattening,[],[f29])).
% 7.41/1.52  
% 7.41/1.52  fof(f53,plain,(
% 7.41/1.52    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.41/1.52    inference(nnf_transformation,[],[f30])).
% 7.41/1.52  
% 7.41/1.52  fof(f54,plain,(
% 7.41/1.52    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.41/1.52    inference(rectify,[],[f53])).
% 7.41/1.52  
% 7.41/1.52  fof(f55,plain,(
% 7.41/1.52    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 7.41/1.52    introduced(choice_axiom,[])).
% 7.41/1.52  
% 7.41/1.52  fof(f56,plain,(
% 7.41/1.52    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.41/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).
% 7.41/1.52  
% 7.41/1.52  fof(f89,plain,(
% 7.41/1.52    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.41/1.52    inference(cnf_transformation,[],[f56])).
% 7.41/1.52  
% 7.41/1.52  fof(f11,axiom,(
% 7.41/1.52    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 7.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.52  
% 7.41/1.52  fof(f32,plain,(
% 7.41/1.52    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.41/1.52    inference(ennf_transformation,[],[f11])).
% 7.41/1.52  
% 7.41/1.52  fof(f33,plain,(
% 7.41/1.52    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.41/1.52    inference(flattening,[],[f32])).
% 7.41/1.52  
% 7.41/1.52  fof(f57,plain,(
% 7.41/1.52    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.41/1.52    inference(nnf_transformation,[],[f33])).
% 7.41/1.52  
% 7.41/1.52  fof(f58,plain,(
% 7.41/1.52    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.41/1.52    inference(flattening,[],[f57])).
% 7.41/1.52  
% 7.41/1.52  fof(f59,plain,(
% 7.41/1.52    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.41/1.52    inference(rectify,[],[f58])).
% 7.41/1.52  
% 7.41/1.52  fof(f60,plain,(
% 7.41/1.52    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) & r2_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 7.41/1.52    introduced(choice_axiom,[])).
% 7.41/1.52  
% 7.41/1.52  fof(f61,plain,(
% 7.41/1.52    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) & r2_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.41/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f59,f60])).
% 7.41/1.52  
% 7.41/1.52  fof(f93,plain,(
% 7.41/1.52    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.41/1.52    inference(cnf_transformation,[],[f61])).
% 7.41/1.52  
% 7.41/1.52  fof(f118,plain,(
% 7.41/1.52    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.41/1.52    inference(equality_resolution,[],[f93])).
% 7.41/1.52  
% 7.41/1.52  fof(f12,axiom,(
% 7.41/1.52    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 7.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.52  
% 7.41/1.52  fof(f34,plain,(
% 7.41/1.52    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 7.41/1.52    inference(ennf_transformation,[],[f12])).
% 7.41/1.52  
% 7.41/1.52  fof(f97,plain,(
% 7.41/1.52    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.41/1.52    inference(cnf_transformation,[],[f34])).
% 7.41/1.52  
% 7.41/1.52  fof(f13,axiom,(
% 7.41/1.52    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 7.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.52  
% 7.41/1.52  fof(f21,plain,(
% 7.41/1.52    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 7.41/1.52    inference(pure_predicate_removal,[],[f13])).
% 7.41/1.52  
% 7.41/1.52  fof(f35,plain,(
% 7.41/1.52    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 7.41/1.52    inference(ennf_transformation,[],[f21])).
% 7.41/1.52  
% 7.41/1.52  fof(f36,plain,(
% 7.41/1.52    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.41/1.52    inference(flattening,[],[f35])).
% 7.41/1.52  
% 7.41/1.52  fof(f98,plain,(
% 7.41/1.52    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.41/1.52    inference(cnf_transformation,[],[f36])).
% 7.41/1.52  
% 7.41/1.52  fof(f109,plain,(
% 7.41/1.52    v1_yellow_0(sK6)),
% 7.41/1.52    inference(cnf_transformation,[],[f72])).
% 7.41/1.52  
% 7.41/1.52  fof(f107,plain,(
% 7.41/1.52    ~v2_struct_0(sK6)),
% 7.41/1.52    inference(cnf_transformation,[],[f72])).
% 7.41/1.52  
% 7.41/1.52  fof(f108,plain,(
% 7.41/1.52    v5_orders_2(sK6)),
% 7.41/1.52    inference(cnf_transformation,[],[f72])).
% 7.41/1.52  
% 7.41/1.52  fof(f10,axiom,(
% 7.41/1.52    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 7.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.52  
% 7.41/1.52  fof(f31,plain,(
% 7.41/1.52    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 7.41/1.52    inference(ennf_transformation,[],[f10])).
% 7.41/1.52  
% 7.41/1.52  fof(f91,plain,(
% 7.41/1.52    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 7.41/1.52    inference(cnf_transformation,[],[f31])).
% 7.41/1.52  
% 7.41/1.52  fof(f88,plain,(
% 7.41/1.52    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.41/1.52    inference(cnf_transformation,[],[f56])).
% 7.41/1.52  
% 7.41/1.52  fof(f87,plain,(
% 7.41/1.52    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.41/1.52    inference(cnf_transformation,[],[f56])).
% 7.41/1.52  
% 7.41/1.52  fof(f113,plain,(
% 7.41/1.52    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 7.41/1.52    inference(cnf_transformation,[],[f72])).
% 7.41/1.52  
% 7.41/1.52  fof(f112,plain,(
% 7.41/1.52    v13_waybel_0(sK7,sK6)),
% 7.41/1.52    inference(cnf_transformation,[],[f72])).
% 7.41/1.52  
% 7.41/1.52  fof(f111,plain,(
% 7.41/1.52    ~v1_xboole_0(sK7)),
% 7.41/1.52    inference(cnf_transformation,[],[f72])).
% 7.41/1.52  
% 7.41/1.52  fof(f15,axiom,(
% 7.41/1.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 7.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.52  
% 7.41/1.52  fof(f39,plain,(
% 7.41/1.52    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.41/1.52    inference(ennf_transformation,[],[f15])).
% 7.41/1.52  
% 7.41/1.52  fof(f67,plain,(
% 7.41/1.52    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.41/1.52    inference(nnf_transformation,[],[f39])).
% 7.41/1.52  
% 7.41/1.52  fof(f105,plain,(
% 7.41/1.52    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.41/1.52    inference(cnf_transformation,[],[f67])).
% 7.41/1.52  
% 7.41/1.52  fof(f120,plain,(
% 7.41/1.52    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 7.41/1.52    inference(equality_resolution,[],[f105])).
% 7.41/1.52  
% 7.41/1.52  fof(f106,plain,(
% 7.41/1.52    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.41/1.52    inference(cnf_transformation,[],[f67])).
% 7.41/1.52  
% 7.41/1.52  fof(f7,axiom,(
% 7.41/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.52  
% 7.41/1.52  fof(f52,plain,(
% 7.41/1.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.41/1.52    inference(nnf_transformation,[],[f7])).
% 7.41/1.52  
% 7.41/1.52  fof(f85,plain,(
% 7.41/1.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.41/1.52    inference(cnf_transformation,[],[f52])).
% 7.41/1.52  
% 7.41/1.52  fof(f3,axiom,(
% 7.41/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.52  
% 7.41/1.52  fof(f46,plain,(
% 7.41/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.41/1.52    inference(nnf_transformation,[],[f3])).
% 7.41/1.52  
% 7.41/1.52  fof(f47,plain,(
% 7.41/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.41/1.52    inference(flattening,[],[f46])).
% 7.41/1.52  
% 7.41/1.52  fof(f76,plain,(
% 7.41/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.41/1.52    inference(cnf_transformation,[],[f47])).
% 7.41/1.52  
% 7.41/1.52  fof(f117,plain,(
% 7.41/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.41/1.52    inference(equality_resolution,[],[f76])).
% 7.41/1.52  
% 7.41/1.52  fof(f92,plain,(
% 7.41/1.52    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.41/1.52    inference(cnf_transformation,[],[f61])).
% 7.41/1.52  
% 7.41/1.52  fof(f119,plain,(
% 7.41/1.52    ( ! [X0,X1] : (r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.41/1.52    inference(equality_resolution,[],[f92])).
% 7.41/1.52  
% 7.41/1.52  fof(f2,axiom,(
% 7.41/1.52    v1_xboole_0(k1_xboole_0)),
% 7.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.52  
% 7.41/1.52  fof(f75,plain,(
% 7.41/1.52    v1_xboole_0(k1_xboole_0)),
% 7.41/1.52    inference(cnf_transformation,[],[f2])).
% 7.41/1.52  
% 7.41/1.52  fof(f115,plain,(
% 7.41/1.52    r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))),
% 7.41/1.52    inference(cnf_transformation,[],[f72])).
% 7.41/1.52  
% 7.41/1.52  fof(f84,plain,(
% 7.41/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.41/1.52    inference(cnf_transformation,[],[f52])).
% 7.41/1.52  
% 7.41/1.52  fof(f6,axiom,(
% 7.41/1.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.52  
% 7.41/1.52  fof(f25,plain,(
% 7.41/1.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.41/1.52    inference(ennf_transformation,[],[f6])).
% 7.41/1.52  
% 7.41/1.52  fof(f26,plain,(
% 7.41/1.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.41/1.52    inference(flattening,[],[f25])).
% 7.41/1.52  
% 7.41/1.52  fof(f83,plain,(
% 7.41/1.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.41/1.52    inference(cnf_transformation,[],[f26])).
% 7.41/1.52  
% 7.41/1.52  fof(f5,axiom,(
% 7.41/1.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 7.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.52  
% 7.41/1.52  fof(f23,plain,(
% 7.41/1.52    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.41/1.52    inference(ennf_transformation,[],[f5])).
% 7.41/1.52  
% 7.41/1.52  fof(f24,plain,(
% 7.41/1.52    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.41/1.52    inference(flattening,[],[f23])).
% 7.41/1.52  
% 7.41/1.52  fof(f48,plain,(
% 7.41/1.52    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.41/1.52    inference(nnf_transformation,[],[f24])).
% 7.41/1.52  
% 7.41/1.52  fof(f49,plain,(
% 7.41/1.52    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.41/1.52    inference(flattening,[],[f48])).
% 7.41/1.52  
% 7.41/1.52  fof(f50,plain,(
% 7.41/1.52    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK1(X0,X1,X2),X2) | ~r2_hidden(sK1(X0,X1,X2),X1)) & (r2_hidden(sK1(X0,X1,X2),X2) | r2_hidden(sK1(X0,X1,X2),X1)) & m1_subset_1(sK1(X0,X1,X2),X0)))),
% 7.41/1.52    introduced(choice_axiom,[])).
% 7.41/1.52  
% 7.41/1.52  fof(f51,plain,(
% 7.41/1.52    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK1(X0,X1,X2),X2) | ~r2_hidden(sK1(X0,X1,X2),X1)) & (r2_hidden(sK1(X0,X1,X2),X2) | r2_hidden(sK1(X0,X1,X2),X1)) & m1_subset_1(sK1(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.41/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).
% 7.41/1.52  
% 7.41/1.52  fof(f82,plain,(
% 7.41/1.52    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(sK1(X0,X1,X2),X2) | ~r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.41/1.52    inference(cnf_transformation,[],[f51])).
% 7.41/1.52  
% 7.41/1.52  fof(f80,plain,(
% 7.41/1.52    ( ! [X2,X0,X1] : (X1 = X2 | m1_subset_1(sK1(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.41/1.52    inference(cnf_transformation,[],[f51])).
% 7.41/1.52  
% 7.41/1.52  fof(f4,axiom,(
% 7.41/1.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 7.41/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.52  
% 7.41/1.52  fof(f22,plain,(
% 7.41/1.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.41/1.52    inference(ennf_transformation,[],[f4])).
% 7.41/1.52  
% 7.41/1.52  fof(f79,plain,(
% 7.41/1.52    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.41/1.52    inference(cnf_transformation,[],[f22])).
% 7.41/1.52  
% 7.41/1.52  fof(f77,plain,(
% 7.41/1.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.41/1.52    inference(cnf_transformation,[],[f47])).
% 7.41/1.52  
% 7.41/1.52  fof(f116,plain,(
% 7.41/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.41/1.52    inference(equality_resolution,[],[f77])).
% 7.41/1.52  
% 7.41/1.52  fof(f114,plain,(
% 7.41/1.52    ~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))),
% 7.41/1.52    inference(cnf_transformation,[],[f72])).
% 7.41/1.52  
% 7.41/1.52  fof(f74,plain,(
% 7.41/1.52    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 7.41/1.52    inference(cnf_transformation,[],[f45])).
% 7.41/1.52  
% 7.41/1.52  cnf(c_1,plain,
% 7.41/1.52      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.41/1.52      inference(cnf_transformation,[],[f73]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_34963,plain,
% 7.41/1.52      ( ~ r2_hidden(sK2(sK6,k1_xboole_0,sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6))),k1_xboole_0)
% 7.41/1.52      | ~ v1_xboole_0(k1_xboole_0) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_1]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_31,plain,
% 7.41/1.52      ( ~ r1_orders_2(X0,X1,X2)
% 7.41/1.52      | ~ v13_waybel_0(X3,X0)
% 7.41/1.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.41/1.52      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.41/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 7.41/1.52      | ~ r2_hidden(X1,X3)
% 7.41/1.52      | r2_hidden(X2,X3)
% 7.41/1.52      | ~ l1_orders_2(X0) ),
% 7.41/1.52      inference(cnf_transformation,[],[f99]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_39,negated_conjecture,
% 7.41/1.52      ( l1_orders_2(sK6) ),
% 7.41/1.52      inference(cnf_transformation,[],[f110]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_822,plain,
% 7.41/1.52      ( ~ r1_orders_2(X0,X1,X2)
% 7.41/1.52      | ~ v13_waybel_0(X3,X0)
% 7.41/1.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.41/1.52      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.41/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 7.41/1.52      | ~ r2_hidden(X1,X3)
% 7.41/1.52      | r2_hidden(X2,X3)
% 7.41/1.52      | sK6 != X0 ),
% 7.41/1.52      inference(resolution_lifted,[status(thm)],[c_31,c_39]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_823,plain,
% 7.41/1.52      ( ~ r1_orders_2(sK6,X0,X1)
% 7.41/1.52      | ~ v13_waybel_0(X2,sK6)
% 7.41/1.52      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.41/1.52      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.41/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.41/1.52      | ~ r2_hidden(X0,X2)
% 7.41/1.52      | r2_hidden(X1,X2) ),
% 7.41/1.52      inference(unflattening,[status(thm)],[c_822]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_13,plain,
% 7.41/1.52      ( m1_subset_1(X0,X1)
% 7.41/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.41/1.52      | ~ r2_hidden(X0,X2) ),
% 7.41/1.52      inference(cnf_transformation,[],[f86]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_839,plain,
% 7.41/1.52      ( ~ r1_orders_2(sK6,X0,X1)
% 7.41/1.52      | ~ v13_waybel_0(X2,sK6)
% 7.41/1.52      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.41/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.41/1.52      | ~ r2_hidden(X0,X2)
% 7.41/1.52      | r2_hidden(X1,X2) ),
% 7.41/1.52      inference(forward_subsumption_resolution,
% 7.41/1.52                [status(thm)],
% 7.41/1.52                [c_823,c_13]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3360,plain,
% 7.41/1.52      ( ~ r1_orders_2(sK6,X0,X1)
% 7.41/1.52      | ~ v13_waybel_0(sK7,sK6)
% 7.41/1.52      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.41/1.52      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.41/1.52      | ~ r2_hidden(X0,sK7)
% 7.41/1.52      | r2_hidden(X1,sK7) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_839]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_10407,plain,
% 7.41/1.52      ( ~ r1_orders_2(sK6,k1_yellow_0(sK6,X0),X1)
% 7.41/1.52      | ~ v13_waybel_0(sK7,sK6)
% 7.41/1.52      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.41/1.52      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.41/1.52      | r2_hidden(X1,sK7)
% 7.41/1.52      | ~ r2_hidden(k1_yellow_0(sK6,X0),sK7) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_3360]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_13944,plain,
% 7.41/1.52      ( ~ r1_orders_2(sK6,k1_yellow_0(sK6,X0),sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)))
% 7.41/1.52      | ~ v13_waybel_0(sK7,sK6)
% 7.41/1.52      | ~ m1_subset_1(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
% 7.41/1.52      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.41/1.52      | r2_hidden(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),sK7)
% 7.41/1.52      | ~ r2_hidden(k1_yellow_0(sK6,X0),sK7) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_10407]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_31792,plain,
% 7.41/1.52      ( ~ r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)))
% 7.41/1.52      | ~ v13_waybel_0(sK7,sK6)
% 7.41/1.52      | ~ m1_subset_1(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
% 7.41/1.52      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.41/1.52      | r2_hidden(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),sK7)
% 7.41/1.52      | ~ r2_hidden(k1_yellow_0(sK6,k1_xboole_0),sK7) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_13944]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_15,plain,
% 7.41/1.52      ( r2_lattice3(X0,X1,X2)
% 7.41/1.52      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.41/1.52      | r2_hidden(sK2(X0,X1,X2),X1)
% 7.41/1.52      | ~ l1_orders_2(X0) ),
% 7.41/1.52      inference(cnf_transformation,[],[f89]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_912,plain,
% 7.41/1.52      ( r2_lattice3(X0,X1,X2)
% 7.41/1.52      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.41/1.52      | r2_hidden(sK2(X0,X1,X2),X1)
% 7.41/1.52      | sK6 != X0 ),
% 7.41/1.52      inference(resolution_lifted,[status(thm)],[c_15,c_39]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_913,plain,
% 7.41/1.52      ( r2_lattice3(sK6,X0,X1)
% 7.41/1.52      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.41/1.52      | r2_hidden(sK2(sK6,X0,X1),X0) ),
% 7.41/1.52      inference(unflattening,[status(thm)],[c_912]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_7746,plain,
% 7.41/1.52      ( r2_lattice3(sK6,X0,sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)))
% 7.41/1.52      | ~ m1_subset_1(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
% 7.41/1.52      | r2_hidden(sK2(sK6,X0,sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6))),X0) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_913]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_23760,plain,
% 7.41/1.52      ( r2_lattice3(sK6,k1_xboole_0,sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)))
% 7.41/1.52      | ~ m1_subset_1(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
% 7.41/1.52      | r2_hidden(sK2(sK6,k1_xboole_0,sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6))),k1_xboole_0) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_7746]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_2194,plain,
% 7.41/1.52      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.41/1.52      theory(equality) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_7917,plain,
% 7.41/1.52      ( r2_hidden(X0,X1)
% 7.41/1.52      | ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 7.41/1.52      | X0 != k3_yellow_0(sK6)
% 7.41/1.52      | X1 != sK7 ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_2194]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_13681,plain,
% 7.41/1.52      ( r2_hidden(X0,sK7)
% 7.41/1.52      | ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 7.41/1.52      | X0 != k3_yellow_0(sK6)
% 7.41/1.52      | sK7 != sK7 ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_7917]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_22682,plain,
% 7.41/1.52      ( r2_hidden(k1_yellow_0(sK6,k1_xboole_0),sK7)
% 7.41/1.52      | ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 7.41/1.52      | k1_yellow_0(sK6,k1_xboole_0) != k3_yellow_0(sK6)
% 7.41/1.52      | sK7 != sK7 ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_13681]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_22,plain,
% 7.41/1.52      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 7.41/1.52      | ~ r2_lattice3(X0,X1,X2)
% 7.41/1.52      | ~ r1_yellow_0(X0,X1)
% 7.41/1.52      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.41/1.52      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 7.41/1.52      | ~ l1_orders_2(X0) ),
% 7.41/1.52      inference(cnf_transformation,[],[f118]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_24,plain,
% 7.41/1.52      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 7.41/1.52      | ~ l1_orders_2(X0) ),
% 7.41/1.52      inference(cnf_transformation,[],[f97]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_259,plain,
% 7.41/1.52      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.41/1.52      | ~ r1_yellow_0(X0,X1)
% 7.41/1.52      | ~ r2_lattice3(X0,X1,X2)
% 7.41/1.52      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 7.41/1.52      | ~ l1_orders_2(X0) ),
% 7.41/1.52      inference(global_propositional_subsumption,
% 7.41/1.52                [status(thm)],
% 7.41/1.52                [c_22,c_24]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_260,plain,
% 7.41/1.52      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 7.41/1.52      | ~ r2_lattice3(X0,X1,X2)
% 7.41/1.52      | ~ r1_yellow_0(X0,X1)
% 7.41/1.52      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.41/1.52      | ~ l1_orders_2(X0) ),
% 7.41/1.52      inference(renaming,[status(thm)],[c_259]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_25,plain,
% 7.41/1.52      ( r1_yellow_0(X0,k1_xboole_0)
% 7.41/1.52      | v2_struct_0(X0)
% 7.41/1.52      | ~ v5_orders_2(X0)
% 7.41/1.52      | ~ v1_yellow_0(X0)
% 7.41/1.52      | ~ l1_orders_2(X0) ),
% 7.41/1.52      inference(cnf_transformation,[],[f98]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_40,negated_conjecture,
% 7.41/1.52      ( v1_yellow_0(sK6) ),
% 7.41/1.52      inference(cnf_transformation,[],[f109]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_581,plain,
% 7.41/1.52      ( r1_yellow_0(X0,k1_xboole_0)
% 7.41/1.52      | v2_struct_0(X0)
% 7.41/1.52      | ~ v5_orders_2(X0)
% 7.41/1.52      | ~ l1_orders_2(X0)
% 7.41/1.52      | sK6 != X0 ),
% 7.41/1.52      inference(resolution_lifted,[status(thm)],[c_25,c_40]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_582,plain,
% 7.41/1.52      ( r1_yellow_0(sK6,k1_xboole_0)
% 7.41/1.52      | v2_struct_0(sK6)
% 7.41/1.52      | ~ v5_orders_2(sK6)
% 7.41/1.52      | ~ l1_orders_2(sK6) ),
% 7.41/1.52      inference(unflattening,[status(thm)],[c_581]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_42,negated_conjecture,
% 7.41/1.52      ( ~ v2_struct_0(sK6) ),
% 7.41/1.52      inference(cnf_transformation,[],[f107]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_41,negated_conjecture,
% 7.41/1.52      ( v5_orders_2(sK6) ),
% 7.41/1.52      inference(cnf_transformation,[],[f108]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_75,plain,
% 7.41/1.52      ( r1_yellow_0(sK6,k1_xboole_0)
% 7.41/1.52      | v2_struct_0(sK6)
% 7.41/1.52      | ~ v5_orders_2(sK6)
% 7.41/1.52      | ~ v1_yellow_0(sK6)
% 7.41/1.52      | ~ l1_orders_2(sK6) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_25]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_584,plain,
% 7.41/1.52      ( r1_yellow_0(sK6,k1_xboole_0) ),
% 7.41/1.52      inference(global_propositional_subsumption,
% 7.41/1.52                [status(thm)],
% 7.41/1.52                [c_582,c_42,c_41,c_40,c_39,c_75]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_721,plain,
% 7.41/1.52      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 7.41/1.52      | ~ r2_lattice3(X0,X1,X2)
% 7.41/1.52      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.41/1.52      | ~ l1_orders_2(X0)
% 7.41/1.52      | sK6 != X0
% 7.41/1.52      | k1_xboole_0 != X1 ),
% 7.41/1.52      inference(resolution_lifted,[status(thm)],[c_260,c_584]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_722,plain,
% 7.41/1.52      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
% 7.41/1.52      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 7.41/1.52      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.41/1.52      | ~ l1_orders_2(sK6) ),
% 7.41/1.52      inference(unflattening,[status(thm)],[c_721]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_726,plain,
% 7.41/1.52      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.41/1.52      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 7.41/1.52      | r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) ),
% 7.41/1.52      inference(global_propositional_subsumption,
% 7.41/1.52                [status(thm)],
% 7.41/1.52                [c_722,c_39]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_727,plain,
% 7.41/1.52      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
% 7.41/1.52      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 7.41/1.52      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 7.41/1.52      inference(renaming,[status(thm)],[c_726]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_14158,plain,
% 7.41/1.52      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)))
% 7.41/1.52      | ~ r2_lattice3(sK6,k1_xboole_0,sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)))
% 7.41/1.52      | ~ m1_subset_1(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6)) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_727]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_18,plain,
% 7.41/1.52      ( ~ l1_orders_2(X0)
% 7.41/1.52      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 7.41/1.52      inference(cnf_transformation,[],[f91]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_871,plain,
% 7.41/1.52      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK6 != X0 ),
% 7.41/1.52      inference(resolution_lifted,[status(thm)],[c_18,c_39]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_872,plain,
% 7.41/1.52      ( k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
% 7.41/1.52      inference(unflattening,[status(thm)],[c_871]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_862,plain,
% 7.41/1.52      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK6 != X0 ),
% 7.41/1.52      inference(resolution_lifted,[status(thm)],[c_24,c_39]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_863,plain,
% 7.41/1.52      ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
% 7.41/1.52      inference(unflattening,[status(thm)],[c_862]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3012,plain,
% 7.41/1.52      ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_863]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3386,plain,
% 7.41/1.52      ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top ),
% 7.41/1.52      inference(superposition,[status(thm)],[c_872,c_3012]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3009,plain,
% 7.41/1.52      ( r2_lattice3(sK6,X0,X1) = iProver_top
% 7.41/1.52      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | r2_hidden(sK2(sK6,X0,X1),X0) = iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_913]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_16,plain,
% 7.41/1.52      ( r2_lattice3(X0,X1,X2)
% 7.41/1.52      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.41/1.52      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 7.41/1.52      | ~ l1_orders_2(X0) ),
% 7.41/1.52      inference(cnf_transformation,[],[f88]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_897,plain,
% 7.41/1.52      ( r2_lattice3(X0,X1,X2)
% 7.41/1.52      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.41/1.52      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 7.41/1.52      | sK6 != X0 ),
% 7.41/1.52      inference(resolution_lifted,[status(thm)],[c_16,c_39]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_898,plain,
% 7.41/1.52      ( r2_lattice3(sK6,X0,X1)
% 7.41/1.52      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.41/1.52      | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6)) ),
% 7.41/1.52      inference(unflattening,[status(thm)],[c_897]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3010,plain,
% 7.41/1.52      ( r2_lattice3(sK6,X0,X1) = iProver_top
% 7.41/1.52      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6)) = iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_898]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_17,plain,
% 7.41/1.52      ( r1_orders_2(X0,X1,X2)
% 7.41/1.52      | ~ r2_lattice3(X0,X3,X2)
% 7.41/1.52      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.41/1.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.41/1.52      | ~ r2_hidden(X1,X3)
% 7.41/1.52      | ~ l1_orders_2(X0) ),
% 7.41/1.52      inference(cnf_transformation,[],[f87]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_876,plain,
% 7.41/1.52      ( r1_orders_2(X0,X1,X2)
% 7.41/1.52      | ~ r2_lattice3(X0,X3,X2)
% 7.41/1.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.41/1.52      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.41/1.52      | ~ r2_hidden(X1,X3)
% 7.41/1.52      | sK6 != X0 ),
% 7.41/1.52      inference(resolution_lifted,[status(thm)],[c_17,c_39]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_877,plain,
% 7.41/1.52      ( r1_orders_2(sK6,X0,X1)
% 7.41/1.52      | ~ r2_lattice3(sK6,X2,X1)
% 7.41/1.52      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.41/1.52      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.41/1.52      | ~ r2_hidden(X0,X2) ),
% 7.41/1.52      inference(unflattening,[status(thm)],[c_876]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3011,plain,
% 7.41/1.52      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 7.41/1.52      | r2_lattice3(sK6,X2,X1) != iProver_top
% 7.41/1.52      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | r2_hidden(X0,X2) != iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_877]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_4673,plain,
% 7.41/1.52      ( r1_orders_2(sK6,sK2(sK6,X0,X1),X2) = iProver_top
% 7.41/1.52      | r2_lattice3(sK6,X3,X2) != iProver_top
% 7.41/1.52      | r2_lattice3(sK6,X0,X1) = iProver_top
% 7.41/1.52      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | r2_hidden(sK2(sK6,X0,X1),X3) != iProver_top ),
% 7.41/1.52      inference(superposition,[status(thm)],[c_3010,c_3011]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_12004,plain,
% 7.41/1.52      ( r1_orders_2(sK6,sK2(sK6,X0,X1),X2) = iProver_top
% 7.41/1.52      | r2_lattice3(sK6,X0,X2) != iProver_top
% 7.41/1.52      | r2_lattice3(sK6,X0,X1) = iProver_top
% 7.41/1.52      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top ),
% 7.41/1.52      inference(superposition,[status(thm)],[c_3009,c_4673]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_36,negated_conjecture,
% 7.41/1.52      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 7.41/1.52      inference(cnf_transformation,[],[f113]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3025,plain,
% 7.41/1.52      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3014,plain,
% 7.41/1.52      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 7.41/1.52      | v13_waybel_0(X2,sK6) != iProver_top
% 7.41/1.52      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 7.41/1.52      | r2_hidden(X0,X2) != iProver_top
% 7.41/1.52      | r2_hidden(X1,X2) = iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_839]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_5806,plain,
% 7.41/1.52      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 7.41/1.52      | v13_waybel_0(sK7,sK6) != iProver_top
% 7.41/1.52      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | r2_hidden(X0,sK7) != iProver_top
% 7.41/1.52      | r2_hidden(X1,sK7) = iProver_top ),
% 7.41/1.52      inference(superposition,[status(thm)],[c_3025,c_3014]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_37,negated_conjecture,
% 7.41/1.52      ( v13_waybel_0(sK7,sK6) ),
% 7.41/1.52      inference(cnf_transformation,[],[f112]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_1050,plain,
% 7.41/1.52      ( ~ r1_orders_2(sK6,X0,X1)
% 7.41/1.52      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.41/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.41/1.52      | ~ r2_hidden(X0,X2)
% 7.41/1.52      | r2_hidden(X1,X2)
% 7.41/1.52      | sK7 != X2
% 7.41/1.52      | sK6 != sK6 ),
% 7.41/1.52      inference(resolution_lifted,[status(thm)],[c_37,c_839]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_1051,plain,
% 7.41/1.52      ( ~ r1_orders_2(sK6,X0,X1)
% 7.41/1.52      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.41/1.52      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.41/1.52      | ~ r2_hidden(X0,sK7)
% 7.41/1.52      | r2_hidden(X1,sK7) ),
% 7.41/1.52      inference(unflattening,[status(thm)],[c_1050]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_1053,plain,
% 7.41/1.52      ( ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.41/1.52      | ~ r1_orders_2(sK6,X0,X1)
% 7.41/1.52      | ~ r2_hidden(X0,sK7)
% 7.41/1.52      | r2_hidden(X1,sK7) ),
% 7.41/1.52      inference(global_propositional_subsumption,
% 7.41/1.52                [status(thm)],
% 7.41/1.52                [c_1051,c_36]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_1054,plain,
% 7.41/1.52      ( ~ r1_orders_2(sK6,X0,X1)
% 7.41/1.52      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.41/1.52      | ~ r2_hidden(X0,sK7)
% 7.41/1.52      | r2_hidden(X1,sK7) ),
% 7.41/1.52      inference(renaming,[status(thm)],[c_1053]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_1055,plain,
% 7.41/1.52      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 7.41/1.52      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | r2_hidden(X0,sK7) != iProver_top
% 7.41/1.52      | r2_hidden(X1,sK7) = iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_1054]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_6089,plain,
% 7.41/1.52      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 7.41/1.52      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | r2_hidden(X0,sK7) != iProver_top
% 7.41/1.52      | r2_hidden(X1,sK7) = iProver_top ),
% 7.41/1.52      inference(global_propositional_subsumption,
% 7.41/1.52                [status(thm)],
% 7.41/1.52                [c_5806,c_1055]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_12121,plain,
% 7.41/1.52      ( r2_lattice3(sK6,X0,X1) != iProver_top
% 7.41/1.52      | r2_lattice3(sK6,X0,X2) = iProver_top
% 7.41/1.52      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | r2_hidden(X1,sK7) = iProver_top
% 7.41/1.52      | r2_hidden(sK2(sK6,X0,X2),sK7) != iProver_top ),
% 7.41/1.52      inference(superposition,[status(thm)],[c_12004,c_6089]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_12160,plain,
% 7.41/1.52      ( r2_lattice3(sK6,sK7,X0) != iProver_top
% 7.41/1.52      | r2_lattice3(sK6,sK7,X1) = iProver_top
% 7.41/1.52      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | r2_hidden(X0,sK7) = iProver_top ),
% 7.41/1.52      inference(superposition,[status(thm)],[c_3009,c_12121]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_38,negated_conjecture,
% 7.41/1.52      ( ~ v1_xboole_0(sK7) ),
% 7.41/1.52      inference(cnf_transformation,[],[f111]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_47,plain,
% 7.41/1.52      ( v1_xboole_0(sK7) != iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_33,plain,
% 7.41/1.52      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 7.41/1.52      inference(cnf_transformation,[],[f120]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_53,plain,
% 7.41/1.52      ( ~ v1_subset_1(sK6,sK6) | ~ m1_subset_1(sK6,k1_zfmisc_1(sK6)) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_33]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_32,plain,
% 7.41/1.52      ( v1_subset_1(X0,X1)
% 7.41/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.41/1.52      | X0 = X1 ),
% 7.41/1.52      inference(cnf_transformation,[],[f106]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_56,plain,
% 7.41/1.52      ( v1_subset_1(sK6,sK6)
% 7.41/1.52      | ~ m1_subset_1(sK6,k1_zfmisc_1(sK6))
% 7.41/1.52      | sK6 = sK6 ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_32]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_96,plain,
% 7.41/1.52      ( ~ l1_orders_2(sK6)
% 7.41/1.52      | k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_18]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_11,plain,
% 7.41/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.41/1.52      inference(cnf_transformation,[],[f85]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_117,plain,
% 7.41/1.52      ( m1_subset_1(sK6,k1_zfmisc_1(sK6)) | ~ r1_tarski(sK6,sK6) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_11]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_5,plain,
% 7.41/1.52      ( r1_tarski(X0,X0) ),
% 7.41/1.52      inference(cnf_transformation,[],[f117]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_133,plain,
% 7.41/1.52      ( r1_tarski(sK6,sK6) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_5]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_2202,plain,
% 7.41/1.52      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 7.41/1.52      theory(equality) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_2217,plain,
% 7.41/1.52      ( k3_yellow_0(sK6) = k3_yellow_0(sK6) | sK6 != sK6 ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_2202]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_2191,plain,( X0 = X0 ),theory(equality) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3489,plain,
% 7.41/1.52      ( sK7 = sK7 ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_2191]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3817,plain,
% 7.41/1.52      ( m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),u1_struct_0(sK6)) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_863]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3818,plain,
% 7.41/1.52      ( m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),u1_struct_0(sK6)) = iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_3817]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_2192,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3449,plain,
% 7.41/1.52      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_2192]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3698,plain,
% 7.41/1.52      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_3449]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_4501,plain,
% 7.41/1.52      ( u1_struct_0(sK6) != sK7 | sK7 = u1_struct_0(sK6) | sK7 != sK7 ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_3698]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3996,plain,
% 7.41/1.52      ( X0 != X1 | X0 = k1_yellow_0(sK6,X2) | k1_yellow_0(sK6,X2) != X1 ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_2192]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_5425,plain,
% 7.41/1.52      ( X0 = k1_yellow_0(sK6,k1_xboole_0)
% 7.41/1.52      | X0 != k3_yellow_0(sK6)
% 7.41/1.52      | k1_yellow_0(sK6,k1_xboole_0) != k3_yellow_0(sK6) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_3996]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_5873,plain,
% 7.41/1.52      ( k1_yellow_0(sK6,k1_xboole_0) != k3_yellow_0(sK6)
% 7.41/1.52      | k3_yellow_0(sK6) = k1_yellow_0(sK6,k1_xboole_0)
% 7.41/1.52      | k3_yellow_0(sK6) != k3_yellow_0(sK6) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_5425]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3018,plain,
% 7.41/1.52      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) = iProver_top
% 7.41/1.52      | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 7.41/1.52      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3140,plain,
% 7.41/1.52      ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
% 7.41/1.52      | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 7.41/1.52      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 7.41/1.52      inference(light_normalisation,[status(thm)],[c_3018,c_872]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_6098,plain,
% 7.41/1.52      ( r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 7.41/1.52      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | r2_hidden(X0,sK7) = iProver_top
% 7.41/1.52      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 7.41/1.52      inference(superposition,[status(thm)],[c_3140,c_6089]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_23,plain,
% 7.41/1.52      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 7.41/1.52      | ~ r1_yellow_0(X0,X1)
% 7.41/1.52      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 7.41/1.52      | ~ l1_orders_2(X0) ),
% 7.41/1.52      inference(cnf_transformation,[],[f119]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_252,plain,
% 7.41/1.52      ( ~ r1_yellow_0(X0,X1)
% 7.41/1.52      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 7.41/1.52      | ~ l1_orders_2(X0) ),
% 7.41/1.52      inference(global_propositional_subsumption,
% 7.41/1.52                [status(thm)],
% 7.41/1.52                [c_23,c_24]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_253,plain,
% 7.41/1.52      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 7.41/1.52      | ~ r1_yellow_0(X0,X1)
% 7.41/1.52      | ~ l1_orders_2(X0) ),
% 7.41/1.52      inference(renaming,[status(thm)],[c_252]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_742,plain,
% 7.41/1.52      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 7.41/1.52      | ~ l1_orders_2(X0)
% 7.41/1.52      | sK6 != X0
% 7.41/1.52      | k1_xboole_0 != X1 ),
% 7.41/1.52      inference(resolution_lifted,[status(thm)],[c_253,c_584]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_743,plain,
% 7.41/1.52      ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0))
% 7.41/1.52      | ~ l1_orders_2(sK6) ),
% 7.41/1.52      inference(unflattening,[status(thm)],[c_742]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_745,plain,
% 7.41/1.52      ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0)) ),
% 7.41/1.52      inference(global_propositional_subsumption,
% 7.41/1.52                [status(thm)],
% 7.41/1.52                [c_743,c_39]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3017,plain,
% 7.41/1.52      ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0)) = iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_745]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3049,plain,
% 7.41/1.52      ( r2_lattice3(sK6,k1_xboole_0,k3_yellow_0(sK6)) = iProver_top ),
% 7.41/1.52      inference(light_normalisation,[status(thm)],[c_3017,c_872]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3026,plain,
% 7.41/1.52      ( m1_subset_1(X0,X1) = iProver_top
% 7.41/1.52      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.41/1.52      | r2_hidden(X0,X2) != iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_5012,plain,
% 7.41/1.52      ( m1_subset_1(X0,u1_struct_0(sK6)) = iProver_top
% 7.41/1.52      | r2_hidden(X0,sK7) != iProver_top ),
% 7.41/1.52      inference(superposition,[status(thm)],[c_3025,c_3026]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_5130,plain,
% 7.41/1.52      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 7.41/1.52      | r2_lattice3(sK6,X2,X1) != iProver_top
% 7.41/1.52      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | r2_hidden(X0,X2) != iProver_top
% 7.41/1.52      | r2_hidden(X0,sK7) != iProver_top ),
% 7.41/1.52      inference(superposition,[status(thm)],[c_5012,c_3011]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_6352,plain,
% 7.41/1.52      ( r1_orders_2(sK6,X0,k3_yellow_0(sK6)) = iProver_top
% 7.41/1.52      | r2_lattice3(sK6,X1,k3_yellow_0(sK6)) != iProver_top
% 7.41/1.52      | r2_hidden(X0,X1) != iProver_top
% 7.41/1.52      | r2_hidden(X0,sK7) != iProver_top ),
% 7.41/1.52      inference(superposition,[status(thm)],[c_3386,c_5130]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_6572,plain,
% 7.41/1.52      ( r1_orders_2(sK6,X0,k3_yellow_0(sK6)) = iProver_top
% 7.41/1.52      | r2_hidden(X0,sK7) != iProver_top
% 7.41/1.52      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.41/1.52      inference(superposition,[status(thm)],[c_3049,c_6352]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_2,plain,
% 7.41/1.52      ( v1_xboole_0(k1_xboole_0) ),
% 7.41/1.52      inference(cnf_transformation,[],[f75]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_625,plain,
% 7.41/1.52      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 7.41/1.52      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_626,plain,
% 7.41/1.52      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.41/1.52      inference(unflattening,[status(thm)],[c_625]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_627,plain,
% 7.41/1.52      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_6591,plain,
% 7.41/1.52      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.41/1.52      inference(global_propositional_subsumption,
% 7.41/1.52                [status(thm)],
% 7.41/1.52                [c_6572,c_627]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_6599,plain,
% 7.41/1.52      ( r2_lattice3(sK6,k1_xboole_0,X0) = iProver_top
% 7.41/1.52      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 7.41/1.52      inference(superposition,[status(thm)],[c_3009,c_6591]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_2197,plain,
% 7.41/1.52      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.41/1.52      theory(equality) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3397,plain,
% 7.41/1.52      ( m1_subset_1(X0,X1)
% 7.41/1.52      | ~ m1_subset_1(k1_yellow_0(sK6,X2),u1_struct_0(sK6))
% 7.41/1.52      | X0 != k1_yellow_0(sK6,X2)
% 7.41/1.52      | X1 != u1_struct_0(sK6) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_2197]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_4958,plain,
% 7.41/1.52      ( m1_subset_1(X0,sK7)
% 7.41/1.52      | ~ m1_subset_1(k1_yellow_0(sK6,X1),u1_struct_0(sK6))
% 7.41/1.52      | X0 != k1_yellow_0(sK6,X1)
% 7.41/1.52      | sK7 != u1_struct_0(sK6) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_3397]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_6866,plain,
% 7.41/1.52      ( ~ m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),u1_struct_0(sK6))
% 7.41/1.52      | m1_subset_1(k3_yellow_0(sK6),sK7)
% 7.41/1.52      | k3_yellow_0(sK6) != k1_yellow_0(sK6,k1_xboole_0)
% 7.41/1.52      | sK7 != u1_struct_0(sK6) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_4958]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_6870,plain,
% 7.41/1.52      ( k3_yellow_0(sK6) != k1_yellow_0(sK6,k1_xboole_0)
% 7.41/1.52      | sK7 != u1_struct_0(sK6)
% 7.41/1.52      | m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | m1_subset_1(k3_yellow_0(sK6),sK7) = iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_6866]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_340,plain,
% 7.41/1.52      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.41/1.52      inference(prop_impl,[status(thm)],[c_11]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_341,plain,
% 7.41/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.41/1.52      inference(renaming,[status(thm)],[c_340]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_433,plain,
% 7.41/1.52      ( v1_subset_1(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 7.41/1.52      inference(bin_hyper_res,[status(thm)],[c_32,c_341]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_34,negated_conjecture,
% 7.41/1.52      ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
% 7.41/1.52      | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 7.41/1.52      inference(cnf_transformation,[],[f115]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_344,plain,
% 7.41/1.52      ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
% 7.41/1.52      | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 7.41/1.52      inference(prop_impl,[status(thm)],[c_34]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_663,plain,
% 7.41/1.52      ( ~ r1_tarski(X0,X1)
% 7.41/1.52      | r2_hidden(k3_yellow_0(sK6),sK7)
% 7.41/1.52      | X1 = X0
% 7.41/1.52      | u1_struct_0(sK6) != X1
% 7.41/1.52      | sK7 != X0 ),
% 7.41/1.52      inference(resolution_lifted,[status(thm)],[c_433,c_344]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_664,plain,
% 7.41/1.52      ( ~ r1_tarski(sK7,u1_struct_0(sK6))
% 7.41/1.52      | r2_hidden(k3_yellow_0(sK6),sK7)
% 7.41/1.52      | u1_struct_0(sK6) = sK7 ),
% 7.41/1.52      inference(unflattening,[status(thm)],[c_663]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3021,plain,
% 7.41/1.52      ( u1_struct_0(sK6) = sK7
% 7.41/1.52      | r1_tarski(sK7,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_49,plain,
% 7.41/1.52      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_665,plain,
% 7.41/1.52      ( u1_struct_0(sK6) = sK7
% 7.41/1.52      | r1_tarski(sK7,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_12,plain,
% 7.41/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.41/1.52      inference(cnf_transformation,[],[f84]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3374,plain,
% 7.41/1.52      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.41/1.52      | r1_tarski(sK7,u1_struct_0(sK6)) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_12]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3375,plain,
% 7.41/1.52      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 7.41/1.52      | r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_3374]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_7840,plain,
% 7.41/1.52      ( u1_struct_0(sK6) = sK7
% 7.41/1.52      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 7.41/1.52      inference(global_propositional_subsumption,
% 7.41/1.52                [status(thm)],
% 7.41/1.52                [c_3021,c_49,c_665,c_3375]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_7848,plain,
% 7.41/1.52      ( u1_struct_0(sK6) = sK7
% 7.41/1.52      | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 7.41/1.52      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | r2_hidden(X0,sK7) = iProver_top ),
% 7.41/1.52      inference(superposition,[status(thm)],[c_7840,c_6098]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_10,plain,
% 7.41/1.52      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.41/1.52      inference(cnf_transformation,[],[f83]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3388,plain,
% 7.41/1.52      ( ~ m1_subset_1(X0,sK7) | r2_hidden(X0,sK7) | v1_xboole_0(sK7) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_10]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_11452,plain,
% 7.41/1.52      ( ~ m1_subset_1(k3_yellow_0(sK6),sK7)
% 7.41/1.52      | r2_hidden(k3_yellow_0(sK6),sK7)
% 7.41/1.52      | v1_xboole_0(sK7) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_3388]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_11453,plain,
% 7.41/1.52      ( m1_subset_1(k3_yellow_0(sK6),sK7) != iProver_top
% 7.41/1.52      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
% 7.41/1.52      | v1_xboole_0(sK7) = iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_11452]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_12220,plain,
% 7.41/1.52      ( m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 7.41/1.52      | r2_hidden(X0,sK7) = iProver_top ),
% 7.41/1.52      inference(global_propositional_subsumption,
% 7.41/1.52                [status(thm)],
% 7.41/1.52                [c_12160,c_39,c_47,c_53,c_56,c_96,c_117,c_133,c_2217,
% 7.41/1.52                 c_3489,c_3818,c_4501,c_5873,c_6098,c_6599,c_6870,c_7848,
% 7.41/1.52                 c_11453]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_12235,plain,
% 7.41/1.52      ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 7.41/1.52      inference(superposition,[status(thm)],[c_3386,c_12220]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_4976,plain,
% 7.41/1.52      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.41/1.52      | r2_hidden(X0,u1_struct_0(sK6))
% 7.41/1.52      | v1_xboole_0(u1_struct_0(sK6)) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_10]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_8590,plain,
% 7.41/1.52      ( ~ m1_subset_1(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
% 7.41/1.52      | r2_hidden(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
% 7.41/1.52      | v1_xboole_0(u1_struct_0(sK6)) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_4976]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_7842,plain,
% 7.41/1.52      ( r2_hidden(k3_yellow_0(sK6),sK7) | u1_struct_0(sK6) = sK7 ),
% 7.41/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_7840]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_7,plain,
% 7.41/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.41/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.41/1.52      | ~ r2_hidden(sK1(X1,X0,X2),X2)
% 7.41/1.52      | ~ r2_hidden(sK1(X1,X0,X2),X0)
% 7.41/1.52      | X0 = X2 ),
% 7.41/1.52      inference(cnf_transformation,[],[f82]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_428,plain,
% 7.41/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.41/1.52      | ~ r1_tarski(X2,X1)
% 7.41/1.52      | ~ r2_hidden(sK1(X1,X2,X0),X0)
% 7.41/1.52      | ~ r2_hidden(sK1(X1,X2,X0),X2)
% 7.41/1.52      | X2 = X0 ),
% 7.41/1.52      inference(bin_hyper_res,[status(thm)],[c_7,c_341]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_1554,plain,
% 7.41/1.52      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.41/1.52      inference(prop_impl,[status(thm)],[c_11]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_1555,plain,
% 7.41/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.41/1.52      inference(renaming,[status(thm)],[c_1554]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_1622,plain,
% 7.41/1.52      ( ~ r1_tarski(X0,X1)
% 7.41/1.52      | ~ r1_tarski(X2,X1)
% 7.41/1.52      | ~ r2_hidden(sK1(X1,X2,X0),X0)
% 7.41/1.52      | ~ r2_hidden(sK1(X1,X2,X0),X2)
% 7.41/1.52      | X2 = X0 ),
% 7.41/1.52      inference(bin_hyper_res,[status(thm)],[c_428,c_1555]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3451,plain,
% 7.41/1.52      ( ~ r1_tarski(X0,X1)
% 7.41/1.52      | ~ r1_tarski(sK7,X1)
% 7.41/1.52      | ~ r2_hidden(sK1(X1,sK7,X0),X0)
% 7.41/1.52      | ~ r2_hidden(sK1(X1,sK7,X0),sK7)
% 7.41/1.52      | sK7 = X0 ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_1622]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3799,plain,
% 7.41/1.52      ( ~ r1_tarski(X0,u1_struct_0(sK6))
% 7.41/1.52      | ~ r1_tarski(sK7,u1_struct_0(sK6))
% 7.41/1.52      | ~ r2_hidden(sK1(u1_struct_0(sK6),sK7,X0),X0)
% 7.41/1.52      | ~ r2_hidden(sK1(u1_struct_0(sK6),sK7,X0),sK7)
% 7.41/1.52      | sK7 = X0 ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_3451]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_4816,plain,
% 7.41/1.52      ( ~ r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6))
% 7.41/1.52      | ~ r1_tarski(sK7,u1_struct_0(sK6))
% 7.41/1.52      | ~ r2_hidden(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
% 7.41/1.52      | ~ r2_hidden(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),sK7)
% 7.41/1.52      | sK7 = u1_struct_0(sK6) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_3799]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_9,plain,
% 7.41/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.41/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.41/1.52      | m1_subset_1(sK1(X1,X0,X2),X1)
% 7.41/1.52      | X0 = X2 ),
% 7.41/1.52      inference(cnf_transformation,[],[f80]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_430,plain,
% 7.41/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.41/1.52      | m1_subset_1(sK1(X1,X2,X0),X1)
% 7.41/1.52      | ~ r1_tarski(X2,X1)
% 7.41/1.52      | X2 = X0 ),
% 7.41/1.52      inference(bin_hyper_res,[status(thm)],[c_9,c_341]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_1624,plain,
% 7.41/1.52      ( m1_subset_1(sK1(X0,X1,X2),X0)
% 7.41/1.52      | ~ r1_tarski(X2,X0)
% 7.41/1.52      | ~ r1_tarski(X1,X0)
% 7.41/1.52      | X1 = X2 ),
% 7.41/1.52      inference(bin_hyper_res,[status(thm)],[c_430,c_1555]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3466,plain,
% 7.41/1.52      ( m1_subset_1(sK1(X0,sK7,X1),X0)
% 7.41/1.52      | ~ r1_tarski(X1,X0)
% 7.41/1.52      | ~ r1_tarski(sK7,X0)
% 7.41/1.52      | sK7 = X1 ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_1624]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3785,plain,
% 7.41/1.52      ( m1_subset_1(sK1(u1_struct_0(sK6),sK7,X0),u1_struct_0(sK6))
% 7.41/1.52      | ~ r1_tarski(X0,u1_struct_0(sK6))
% 7.41/1.52      | ~ r1_tarski(sK7,u1_struct_0(sK6))
% 7.41/1.52      | sK7 = X0 ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_3466]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_4706,plain,
% 7.41/1.52      ( m1_subset_1(sK1(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),u1_struct_0(sK6))
% 7.41/1.52      | ~ r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6))
% 7.41/1.52      | ~ r1_tarski(sK7,u1_struct_0(sK6))
% 7.41/1.52      | sK7 = u1_struct_0(sK6) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_3785]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_4364,plain,
% 7.41/1.52      ( ~ r2_hidden(sK0(sK7),u1_struct_0(sK6))
% 7.41/1.52      | ~ v1_xboole_0(u1_struct_0(sK6)) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_1]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_6,plain,
% 7.41/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.41/1.52      | ~ r2_hidden(X2,X0)
% 7.41/1.52      | r2_hidden(X2,X1) ),
% 7.41/1.52      inference(cnf_transformation,[],[f79]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_427,plain,
% 7.41/1.52      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 7.41/1.52      inference(bin_hyper_res,[status(thm)],[c_6,c_341]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3439,plain,
% 7.41/1.52      ( ~ r1_tarski(sK7,X0)
% 7.41/1.52      | r2_hidden(sK0(sK7),X0)
% 7.41/1.52      | ~ r2_hidden(sK0(sK7),sK7) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_427]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3786,plain,
% 7.41/1.52      ( ~ r1_tarski(sK7,u1_struct_0(sK6))
% 7.41/1.52      | r2_hidden(sK0(sK7),u1_struct_0(sK6))
% 7.41/1.52      | ~ r2_hidden(sK0(sK7),sK7) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_3439]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_4,plain,
% 7.41/1.52      ( r1_tarski(X0,X0) ),
% 7.41/1.52      inference(cnf_transformation,[],[f116]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3508,plain,
% 7.41/1.52      ( r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6)) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_4]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3511,plain,
% 7.41/1.52      ( r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6)) = iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_3508]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3369,plain,
% 7.41/1.52      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.41/1.52      | ~ r1_tarski(X0,u1_struct_0(sK6)) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_11]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3507,plain,
% 7.41/1.52      ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
% 7.41/1.52      | ~ r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6)) ),
% 7.41/1.52      inference(instantiation,[status(thm)],[c_3369]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_3509,plain,
% 7.41/1.52      ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 7.41/1.52      | r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6)) != iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_3507]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_35,negated_conjecture,
% 7.41/1.52      ( v1_subset_1(sK7,u1_struct_0(sK6))
% 7.41/1.52      | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 7.41/1.52      inference(cnf_transformation,[],[f114]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_342,plain,
% 7.41/1.52      ( v1_subset_1(sK7,u1_struct_0(sK6))
% 7.41/1.52      | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 7.41/1.52      inference(prop_impl,[status(thm)],[c_35]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_676,plain,
% 7.41/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 7.41/1.52      | ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 7.41/1.52      | u1_struct_0(sK6) != X0
% 7.41/1.52      | sK7 != X0 ),
% 7.41/1.52      inference(resolution_lifted,[status(thm)],[c_33,c_342]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_677,plain,
% 7.41/1.52      ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
% 7.41/1.52      | ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 7.41/1.52      | sK7 != u1_struct_0(sK6) ),
% 7.41/1.52      inference(unflattening,[status(thm)],[c_676]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_678,plain,
% 7.41/1.52      ( sK7 != u1_struct_0(sK6)
% 7.41/1.52      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 7.41/1.52      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 7.41/1.52      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_0,plain,
% 7.41/1.52      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 7.41/1.52      inference(cnf_transformation,[],[f74]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_618,plain,
% 7.41/1.52      ( r2_hidden(sK0(X0),X0) | sK7 != X0 ),
% 7.41/1.52      inference(resolution_lifted,[status(thm)],[c_0,c_38]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(c_619,plain,
% 7.41/1.52      ( r2_hidden(sK0(sK7),sK7) ),
% 7.41/1.52      inference(unflattening,[status(thm)],[c_618]) ).
% 7.41/1.52  
% 7.41/1.52  cnf(contradiction,plain,
% 7.41/1.52      ( $false ),
% 7.41/1.52      inference(minisat,
% 7.41/1.52                [status(thm)],
% 7.41/1.52                [c_34963,c_31792,c_23760,c_22682,c_14158,c_12235,c_8590,
% 7.41/1.52                 c_7842,c_4816,c_4706,c_4501,c_4364,c_3786,c_3511,c_3508,
% 7.41/1.52                 c_3509,c_3489,c_3374,c_678,c_619,c_2,c_96,c_36,c_37,
% 7.41/1.52                 c_39]) ).
% 7.41/1.52  
% 7.41/1.52  
% 7.41/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.41/1.52  
% 7.41/1.52  ------                               Statistics
% 7.41/1.52  
% 7.41/1.52  ------ General
% 7.41/1.52  
% 7.41/1.52  abstr_ref_over_cycles:                  0
% 7.41/1.52  abstr_ref_under_cycles:                 0
% 7.41/1.52  gc_basic_clause_elim:                   0
% 7.41/1.52  forced_gc_time:                         0
% 7.41/1.52  parsing_time:                           0.014
% 7.41/1.52  unif_index_cands_time:                  0.
% 7.41/1.52  unif_index_add_time:                    0.
% 7.41/1.52  orderings_time:                         0.
% 7.41/1.52  out_proof_time:                         0.015
% 7.41/1.52  total_time:                             1.02
% 7.41/1.52  num_of_symbols:                         57
% 7.41/1.52  num_of_terms:                           20222
% 7.41/1.52  
% 7.41/1.52  ------ Preprocessing
% 7.41/1.52  
% 7.41/1.52  num_of_splits:                          0
% 7.41/1.52  num_of_split_atoms:                     0
% 7.41/1.52  num_of_reused_defs:                     0
% 7.41/1.52  num_eq_ax_congr_red:                    39
% 7.41/1.52  num_of_sem_filtered_clauses:            1
% 7.41/1.52  num_of_subtypes:                        0
% 7.41/1.52  monotx_restored_types:                  0
% 7.41/1.52  sat_num_of_epr_types:                   0
% 7.41/1.52  sat_num_of_non_cyclic_types:            0
% 7.41/1.52  sat_guarded_non_collapsed_types:        0
% 7.41/1.52  num_pure_diseq_elim:                    0
% 7.41/1.52  simp_replaced_by:                       0
% 7.41/1.52  res_preprocessed:                       182
% 7.41/1.52  prep_upred:                             0
% 7.41/1.52  prep_unflattend:                        74
% 7.41/1.52  smt_new_axioms:                         0
% 7.41/1.52  pred_elim_cands:                        7
% 7.41/1.52  pred_elim:                              6
% 7.41/1.52  pred_elim_cl:                           7
% 7.41/1.52  pred_elim_cycles:                       12
% 7.41/1.52  merged_defs:                            10
% 7.41/1.52  merged_defs_ncl:                        0
% 7.41/1.52  bin_hyper_res:                          18
% 7.41/1.52  prep_cycles:                            4
% 7.41/1.52  pred_elim_time:                         0.056
% 7.41/1.52  splitting_time:                         0.
% 7.41/1.52  sem_filter_time:                        0.
% 7.41/1.52  monotx_time:                            0.001
% 7.41/1.52  subtype_inf_time:                       0.
% 7.41/1.52  
% 7.41/1.52  ------ Problem properties
% 7.41/1.52  
% 7.41/1.52  clauses:                                35
% 7.41/1.52  conjectures:                            3
% 7.41/1.52  epr:                                    8
% 7.41/1.52  horn:                                   22
% 7.41/1.52  ground:                                 8
% 7.41/1.52  unary:                                  8
% 7.41/1.52  binary:                                 4
% 7.41/1.52  lits:                                   98
% 7.41/1.52  lits_eq:                                10
% 7.41/1.52  fd_pure:                                0
% 7.41/1.52  fd_pseudo:                              0
% 7.41/1.52  fd_cond:                                3
% 7.41/1.52  fd_pseudo_cond:                         4
% 7.41/1.52  ac_symbols:                             0
% 7.41/1.52  
% 7.41/1.52  ------ Propositional Solver
% 7.41/1.52  
% 7.41/1.52  prop_solver_calls:                      33
% 7.41/1.52  prop_fast_solver_calls:                 2602
% 7.41/1.52  smt_solver_calls:                       0
% 7.41/1.52  smt_fast_solver_calls:                  0
% 7.41/1.52  prop_num_of_clauses:                    9150
% 7.41/1.52  prop_preprocess_simplified:             18584
% 7.41/1.52  prop_fo_subsumed:                       66
% 7.41/1.52  prop_solver_time:                       0.
% 7.41/1.52  smt_solver_time:                        0.
% 7.41/1.52  smt_fast_solver_time:                   0.
% 7.41/1.52  prop_fast_solver_time:                  0.
% 7.41/1.52  prop_unsat_core_time:                   0.
% 7.41/1.52  
% 7.41/1.52  ------ QBF
% 7.41/1.52  
% 7.41/1.52  qbf_q_res:                              0
% 7.41/1.52  qbf_num_tautologies:                    0
% 7.41/1.52  qbf_prep_cycles:                        0
% 7.41/1.52  
% 7.41/1.52  ------ BMC1
% 7.41/1.52  
% 7.41/1.52  bmc1_current_bound:                     -1
% 7.41/1.52  bmc1_last_solved_bound:                 -1
% 7.41/1.52  bmc1_unsat_core_size:                   -1
% 7.41/1.52  bmc1_unsat_core_parents_size:           -1
% 7.41/1.52  bmc1_merge_next_fun:                    0
% 7.41/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.41/1.52  
% 7.41/1.52  ------ Instantiation
% 7.41/1.52  
% 7.41/1.52  inst_num_of_clauses:                    2135
% 7.41/1.52  inst_num_in_passive:                    603
% 7.41/1.52  inst_num_in_active:                     1139
% 7.41/1.52  inst_num_in_unprocessed:                394
% 7.41/1.52  inst_num_of_loops:                      1352
% 7.41/1.52  inst_num_of_learning_restarts:          0
% 7.41/1.52  inst_num_moves_active_passive:          207
% 7.41/1.52  inst_lit_activity:                      0
% 7.41/1.52  inst_lit_activity_moves:                1
% 7.41/1.52  inst_num_tautologies:                   0
% 7.41/1.52  inst_num_prop_implied:                  0
% 7.41/1.52  inst_num_existing_simplified:           0
% 7.41/1.52  inst_num_eq_res_simplified:             0
% 7.41/1.52  inst_num_child_elim:                    0
% 7.41/1.52  inst_num_of_dismatching_blockings:      1187
% 7.41/1.52  inst_num_of_non_proper_insts:           3710
% 7.41/1.52  inst_num_of_duplicates:                 0
% 7.41/1.52  inst_inst_num_from_inst_to_res:         0
% 7.41/1.52  inst_dismatching_checking_time:         0.
% 7.41/1.52  
% 7.41/1.52  ------ Resolution
% 7.41/1.52  
% 7.41/1.52  res_num_of_clauses:                     0
% 7.41/1.52  res_num_in_passive:                     0
% 7.41/1.52  res_num_in_active:                      0
% 7.41/1.52  res_num_of_loops:                       186
% 7.41/1.52  res_forward_subset_subsumed:            515
% 7.41/1.52  res_backward_subset_subsumed:           6
% 7.41/1.52  res_forward_subsumed:                   0
% 7.41/1.52  res_backward_subsumed:                  0
% 7.41/1.52  res_forward_subsumption_resolution:     6
% 7.41/1.52  res_backward_subsumption_resolution:    0
% 7.41/1.52  res_clause_to_clause_subsumption:       6414
% 7.41/1.52  res_orphan_elimination:                 0
% 7.41/1.52  res_tautology_del:                      289
% 7.41/1.52  res_num_eq_res_simplified:              0
% 7.41/1.52  res_num_sel_changes:                    0
% 7.41/1.52  res_moves_from_active_to_pass:          0
% 7.41/1.52  
% 7.41/1.52  ------ Superposition
% 7.41/1.52  
% 7.41/1.52  sup_time_total:                         0.
% 7.41/1.52  sup_time_generating:                    0.
% 7.41/1.52  sup_time_sim_full:                      0.
% 7.41/1.52  sup_time_sim_immed:                     0.
% 7.41/1.52  
% 7.41/1.52  sup_num_of_clauses:                     972
% 7.41/1.52  sup_num_in_active:                      270
% 7.41/1.52  sup_num_in_passive:                     702
% 7.41/1.52  sup_num_of_loops:                       270
% 7.41/1.52  sup_fw_superposition:                   551
% 7.41/1.52  sup_bw_superposition:                   785
% 7.41/1.52  sup_immediate_simplified:               258
% 7.41/1.52  sup_given_eliminated:                   0
% 7.41/1.52  comparisons_done:                       0
% 7.41/1.52  comparisons_avoided:                    0
% 7.41/1.52  
% 7.41/1.52  ------ Simplifications
% 7.41/1.52  
% 7.41/1.52  
% 7.41/1.52  sim_fw_subset_subsumed:                 69
% 7.41/1.52  sim_bw_subset_subsumed:                 5
% 7.41/1.52  sim_fw_subsumed:                        145
% 7.41/1.52  sim_bw_subsumed:                        7
% 7.41/1.52  sim_fw_subsumption_res:                 3
% 7.41/1.52  sim_bw_subsumption_res:                 16
% 7.41/1.52  sim_tautology_del:                      67
% 7.41/1.52  sim_eq_tautology_del:                   14
% 7.41/1.52  sim_eq_res_simp:                        0
% 7.41/1.52  sim_fw_demodulated:                     4
% 7.41/1.52  sim_bw_demodulated:                     0
% 7.41/1.52  sim_light_normalised:                   24
% 7.41/1.52  sim_joinable_taut:                      0
% 7.41/1.52  sim_joinable_simp:                      0
% 7.41/1.52  sim_ac_normalised:                      0
% 7.41/1.52  sim_smt_subsumption:                    0
% 7.41/1.52  
%------------------------------------------------------------------------------
