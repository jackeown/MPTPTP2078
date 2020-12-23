%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:30 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :  233 (1277 expanded)
%              Number of clauses        :  136 ( 321 expanded)
%              Number of leaves         :   27 ( 250 expanded)
%              Depth                    :   27
%              Number of atoms          :  981 (10007 expanded)
%              Number of equality atoms :  244 ( 462 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f47])).

fof(f73,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | m1_subset_1(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f49,plain,(
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

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f43,plain,(
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
    inference(flattening,[],[f43])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f65,plain,(
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
    inference(flattening,[],[f64])).

fof(f67,plain,(
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

fof(f66,plain,
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

fof(f68,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f65,f67,f66])).

fof(f102,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f105,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f68])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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
    inference(flattening,[],[f40])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f59,plain,(
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
    inference(rectify,[],[f58])).

fof(f61,plain,(
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

fof(f60,plain,(
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

fof(f62,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f59,f61,f60])).

fof(f91,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

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

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f104,plain,(
    v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

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

fof(f53,plain,(
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

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f108,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f85])).

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

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f90,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f101,plain,(
    v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f99,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f100,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f68])).

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

fof(f83,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f45])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f103,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f68])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f107,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | ~ v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f68])).

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

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f97,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f110,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f97])).

fof(f106,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK1(X1,X0),X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2572,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_843,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_35])).

cnf(c_844,plain,
    ( r2_lattice3(sK6,X0,X1)
    | r2_hidden(sK2(sK6,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_843])).

cnf(c_2552,plain,
    ( r2_lattice3(sK6,X0,X1) = iProver_top
    | r2_hidden(sK2(sK6,X0,X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_844])).

cnf(c_12,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_828,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_35])).

cnf(c_829,plain,
    ( r2_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_828])).

cnf(c_2553,plain,
    ( r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_829])).

cnf(c_13,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_807,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_35])).

cnf(c_808,plain,
    ( r1_orders_2(sK6,X0,X1)
    | ~ r2_lattice3(sK6,X2,X1)
    | ~ r2_hidden(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_807])).

cnf(c_2554,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r2_lattice3(sK6,X2,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_808])).

cnf(c_3744,plain,
    ( r1_orders_2(sK6,sK2(sK6,X0,X1),X2) = iProver_top
    | r2_lattice3(sK6,X3,X2) != iProver_top
    | r2_lattice3(sK6,X0,X1) = iProver_top
    | r2_hidden(sK2(sK6,X0,X1),X3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2553,c_2554])).

cnf(c_7669,plain,
    ( r1_orders_2(sK6,sK2(sK6,X0,X1),X2) = iProver_top
    | r2_lattice3(sK6,X0,X2) != iProver_top
    | r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2552,c_3744])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2567,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_27,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_753,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_35])).

cnf(c_754,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(X2,sK6)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(unflattening,[status(thm)],[c_753])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_770,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(X2,sK6)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_754,c_8])).

cnf(c_2557,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK6) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_770])).

cnf(c_4186,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2567,c_2557])).

cnf(c_45,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_33,negated_conjecture,
    ( v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_981,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | sK7 != X2
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_770])).

cnf(c_982,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(unflattening,[status(thm)],[c_981])).

cnf(c_983,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_982])).

cnf(c_4364,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4186,c_45,c_983])).

cnf(c_8034,plain,
    ( r2_lattice3(sK6,X0,X1) != iProver_top
    | r2_lattice3(sK6,X0,X2) = iProver_top
    | r2_hidden(X1,sK7) = iProver_top
    | r2_hidden(sK2(sK6,X0,X2),sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7669,c_4364])).

cnf(c_8041,plain,
    ( r2_lattice3(sK6,sK7,X0) != iProver_top
    | r2_lattice3(sK6,sK7,X1) = iProver_top
    | r2_hidden(X0,sK7) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2552,c_8034])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_133,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_18,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_20,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_239,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_20])).

cnf(c_240,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_239])).

cnf(c_21,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_36,negated_conjecture,
    ( v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_525,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_36])).

cnf(c_526,plain,
    ( r1_yellow_0(sK6,k1_xboole_0)
    | v2_struct_0(sK6)
    | ~ v5_orders_2(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_37,negated_conjecture,
    ( v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_71,plain,
    ( r1_yellow_0(sK6,k1_xboole_0)
    | v2_struct_0(sK6)
    | ~ v5_orders_2(sK6)
    | ~ v1_yellow_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_528,plain,
    ( r1_yellow_0(sK6,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_526,c_38,c_37,c_36,c_35,c_71])).

cnf(c_628,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK6 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_240,c_528])).

cnf(c_629,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
    | ~ r2_lattice3(sK6,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_633,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_lattice3(sK6,k1_xboole_0,X0)
    | r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_35])).

cnf(c_634,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
    | ~ r2_lattice3(sK6,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_633])).

cnf(c_2562,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) = iProver_top
    | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_14,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_802,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_35])).

cnf(c_803,plain,
    ( k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
    inference(unflattening,[status(thm)],[c_802])).

cnf(c_2579,plain,
    ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
    | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2562,c_803])).

cnf(c_4369,plain,
    ( r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2579,c_4364])).

cnf(c_2577,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2576,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2575,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2568,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3918,plain,
    ( r2_hidden(X0,k2_subset_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2576,c_2568])).

cnf(c_4728,plain,
    ( k2_subset_1(X0) = k1_xboole_0
    | m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2575,c_3918])).

cnf(c_5688,plain,
    ( k2_subset_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2576,c_4728])).

cnf(c_6028,plain,
    ( k2_subset_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2577,c_5688])).

cnf(c_4729,plain,
    ( r2_lattice3(sK6,k2_subset_1(X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2552,c_3918])).

cnf(c_6157,plain,
    ( r2_lattice3(sK6,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6028,c_4729])).

cnf(c_19,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_232,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_20])).

cnf(c_233,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_232])).

cnf(c_649,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0)
    | sK6 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_233,c_528])).

cnf(c_650,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_649])).

cnf(c_652,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_650,c_35])).

cnf(c_2561,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_652])).

cnf(c_2578,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k3_yellow_0(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2561,c_803])).

cnf(c_793,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_35])).

cnf(c_794,plain,
    ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_793])).

cnf(c_2555,plain,
    ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_2929,plain,
    ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_2555])).

cnf(c_2569,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4238,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2567,c_2569])).

cnf(c_4358,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r2_lattice3(sK6,X2,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4238,c_2554])).

cnf(c_4640,plain,
    ( r1_orders_2(sK6,X0,k3_yellow_0(sK6)) = iProver_top
    | r2_lattice3(sK6,X1,k3_yellow_0(sK6)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2929,c_4358])).

cnf(c_4840,plain,
    ( r1_orders_2(sK6,X0,k3_yellow_0(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2578,c_4640])).

cnf(c_5114,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
    | m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4840,c_4364])).

cnf(c_5123,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5114,c_2929])).

cnf(c_5124,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_5123])).

cnf(c_5129,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK0(X0,sK7),k1_xboole_0) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2575,c_5124])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_43,plain,
    ( v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_28,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_30,negated_conjecture,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_310,plain,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(prop_impl,[status(thm)],[c_30])).

cnf(c_594,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0
    | u1_struct_0(sK6) != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_310])).

cnf(c_595,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | u1_struct_0(sK6) = sK7 ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_596,plain,
    ( u1_struct_0(sK6) = sK7
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_2027,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_2041,plain,
    ( k3_yellow_0(sK6) = k3_yellow_0(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2027])).

cnf(c_2017,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2048,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_2017])).

cnf(c_4086,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_2017])).

cnf(c_2018,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3205,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_2018])).

cnf(c_4090,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3205])).

cnf(c_5399,plain,
    ( u1_struct_0(sK6) != sK7
    | sK7 = u1_struct_0(sK6)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_4090])).

cnf(c_2021,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3955,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
    | X0 != k3_yellow_0(sK6)
    | X1 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2021])).

cnf(c_4818,plain,
    ( m1_subset_1(k3_yellow_0(sK6),X0)
    | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
    | X0 != u1_struct_0(sK6)
    | k3_yellow_0(sK6) != k3_yellow_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3955])).

cnf(c_5850,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
    | m1_subset_1(k3_yellow_0(sK6),sK7)
    | k3_yellow_0(sK6) != k3_yellow_0(sK6)
    | sK7 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4818])).

cnf(c_5851,plain,
    ( k3_yellow_0(sK6) != k3_yellow_0(sK6)
    | sK7 != u1_struct_0(sK6)
    | m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5850])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2647,plain,
    ( r2_hidden(X0,sK7)
    | ~ m1_subset_1(X0,sK7)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6977,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | ~ m1_subset_1(k3_yellow_0(sK6),sK7)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_2647])).

cnf(c_6978,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
    | m1_subset_1(k3_yellow_0(sK6),sK7) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6977])).

cnf(c_7677,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5129,c_43,c_45,c_596,c_2041,c_2048,c_2929,c_4086,c_5399,c_5851,c_6978])).

cnf(c_8067,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8041,c_43,c_45,c_133,c_596,c_2041,c_2048,c_2929,c_4086,c_4369,c_5399,c_5851,c_6157,c_6978])).

cnf(c_8074,plain,
    ( u1_struct_0(sK6) = X0
    | r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2572,c_8067])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2573,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9493,plain,
    ( u1_struct_0(sK6) = sK7
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8074,c_2573])).

cnf(c_7679,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7677])).

cnf(c_2673,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | X2 != X0
    | k1_zfmisc_1(u1_struct_0(sK6)) != X1 ),
    inference(instantiation,[status(thm)],[c_2021])).

cnf(c_3033,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | X1 != X0
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2673])).

cnf(c_4215,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | X0 != sK7
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3033])).

cnf(c_5019,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | u1_struct_0(sK6) != sK7
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_4215])).

cnf(c_3470,plain,
    ( k1_zfmisc_1(u1_struct_0(sK6)) = k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2017])).

cnf(c_29,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_31,negated_conjecture,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_308,plain,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(prop_impl,[status(thm)],[c_31])).

cnf(c_608,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | u1_struct_0(sK6) != X0
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_308])).

cnf(c_609,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | sK7 != u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9493,c_7679,c_5399,c_5019,c_4086,c_3470,c_609,c_45,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.93/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/0.93  
% 3.93/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.93/0.93  
% 3.93/0.93  ------  iProver source info
% 3.93/0.93  
% 3.93/0.93  git: date: 2020-06-30 10:37:57 +0100
% 3.93/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.93/0.93  git: non_committed_changes: false
% 3.93/0.93  git: last_make_outside_of_git: false
% 3.93/0.93  
% 3.93/0.93  ------ 
% 3.93/0.93  
% 3.93/0.93  ------ Input Options
% 3.93/0.93  
% 3.93/0.93  --out_options                           all
% 3.93/0.93  --tptp_safe_out                         true
% 3.93/0.93  --problem_path                          ""
% 3.93/0.93  --include_path                          ""
% 3.93/0.93  --clausifier                            res/vclausify_rel
% 3.93/0.93  --clausifier_options                    ""
% 3.93/0.93  --stdin                                 false
% 3.93/0.93  --stats_out                             all
% 3.93/0.93  
% 3.93/0.93  ------ General Options
% 3.93/0.93  
% 3.93/0.93  --fof                                   false
% 3.93/0.93  --time_out_real                         305.
% 3.93/0.93  --time_out_virtual                      -1.
% 3.93/0.93  --symbol_type_check                     false
% 3.93/0.93  --clausify_out                          false
% 3.93/0.93  --sig_cnt_out                           false
% 3.93/0.93  --trig_cnt_out                          false
% 3.93/0.93  --trig_cnt_out_tolerance                1.
% 3.93/0.93  --trig_cnt_out_sk_spl                   false
% 3.93/0.93  --abstr_cl_out                          false
% 3.93/0.93  
% 3.93/0.93  ------ Global Options
% 3.93/0.93  
% 3.93/0.93  --schedule                              default
% 3.93/0.93  --add_important_lit                     false
% 3.93/0.93  --prop_solver_per_cl                    1000
% 3.93/0.93  --min_unsat_core                        false
% 3.93/0.93  --soft_assumptions                      false
% 3.93/0.93  --soft_lemma_size                       3
% 3.93/0.93  --prop_impl_unit_size                   0
% 3.93/0.93  --prop_impl_unit                        []
% 3.93/0.93  --share_sel_clauses                     true
% 3.93/0.93  --reset_solvers                         false
% 3.93/0.93  --bc_imp_inh                            [conj_cone]
% 3.93/0.93  --conj_cone_tolerance                   3.
% 3.93/0.93  --extra_neg_conj                        none
% 3.93/0.93  --large_theory_mode                     true
% 3.93/0.93  --prolific_symb_bound                   200
% 3.93/0.93  --lt_threshold                          2000
% 3.93/0.93  --clause_weak_htbl                      true
% 3.93/0.93  --gc_record_bc_elim                     false
% 3.93/0.93  
% 3.93/0.93  ------ Preprocessing Options
% 3.93/0.93  
% 3.93/0.93  --preprocessing_flag                    true
% 3.93/0.93  --time_out_prep_mult                    0.1
% 3.93/0.93  --splitting_mode                        input
% 3.93/0.93  --splitting_grd                         true
% 3.93/0.93  --splitting_cvd                         false
% 3.93/0.93  --splitting_cvd_svl                     false
% 3.93/0.93  --splitting_nvd                         32
% 3.93/0.93  --sub_typing                            true
% 3.93/0.93  --prep_gs_sim                           true
% 3.93/0.93  --prep_unflatten                        true
% 3.93/0.93  --prep_res_sim                          true
% 3.93/0.93  --prep_upred                            true
% 3.93/0.93  --prep_sem_filter                       exhaustive
% 3.93/0.93  --prep_sem_filter_out                   false
% 3.93/0.93  --pred_elim                             true
% 3.93/0.93  --res_sim_input                         true
% 3.93/0.93  --eq_ax_congr_red                       true
% 3.93/0.93  --pure_diseq_elim                       true
% 3.93/0.93  --brand_transform                       false
% 3.93/0.93  --non_eq_to_eq                          false
% 3.93/0.93  --prep_def_merge                        true
% 3.93/0.93  --prep_def_merge_prop_impl              false
% 3.93/0.93  --prep_def_merge_mbd                    true
% 3.93/0.93  --prep_def_merge_tr_red                 false
% 3.93/0.93  --prep_def_merge_tr_cl                  false
% 3.93/0.93  --smt_preprocessing                     true
% 3.93/0.93  --smt_ac_axioms                         fast
% 3.93/0.93  --preprocessed_out                      false
% 3.93/0.93  --preprocessed_stats                    false
% 3.93/0.93  
% 3.93/0.93  ------ Abstraction refinement Options
% 3.93/0.93  
% 3.93/0.93  --abstr_ref                             []
% 3.93/0.93  --abstr_ref_prep                        false
% 3.93/0.93  --abstr_ref_until_sat                   false
% 3.93/0.93  --abstr_ref_sig_restrict                funpre
% 3.93/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.93/0.93  --abstr_ref_under                       []
% 3.93/0.93  
% 3.93/0.93  ------ SAT Options
% 3.93/0.93  
% 3.93/0.93  --sat_mode                              false
% 3.93/0.93  --sat_fm_restart_options                ""
% 3.93/0.93  --sat_gr_def                            false
% 3.93/0.93  --sat_epr_types                         true
% 3.93/0.93  --sat_non_cyclic_types                  false
% 3.93/0.93  --sat_finite_models                     false
% 3.93/0.93  --sat_fm_lemmas                         false
% 3.93/0.93  --sat_fm_prep                           false
% 3.93/0.93  --sat_fm_uc_incr                        true
% 3.93/0.93  --sat_out_model                         small
% 3.93/0.93  --sat_out_clauses                       false
% 3.93/0.93  
% 3.93/0.93  ------ QBF Options
% 3.93/0.93  
% 3.93/0.93  --qbf_mode                              false
% 3.93/0.93  --qbf_elim_univ                         false
% 3.93/0.93  --qbf_dom_inst                          none
% 3.93/0.93  --qbf_dom_pre_inst                      false
% 3.93/0.93  --qbf_sk_in                             false
% 3.93/0.93  --qbf_pred_elim                         true
% 3.93/0.93  --qbf_split                             512
% 3.93/0.93  
% 3.93/0.93  ------ BMC1 Options
% 3.93/0.93  
% 3.93/0.93  --bmc1_incremental                      false
% 3.93/0.93  --bmc1_axioms                           reachable_all
% 3.93/0.93  --bmc1_min_bound                        0
% 3.93/0.93  --bmc1_max_bound                        -1
% 3.93/0.93  --bmc1_max_bound_default                -1
% 3.93/0.93  --bmc1_symbol_reachability              true
% 3.93/0.93  --bmc1_property_lemmas                  false
% 3.93/0.93  --bmc1_k_induction                      false
% 3.93/0.93  --bmc1_non_equiv_states                 false
% 3.93/0.93  --bmc1_deadlock                         false
% 3.93/0.93  --bmc1_ucm                              false
% 3.93/0.93  --bmc1_add_unsat_core                   none
% 3.93/0.93  --bmc1_unsat_core_children              false
% 3.93/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.93/0.93  --bmc1_out_stat                         full
% 3.93/0.93  --bmc1_ground_init                      false
% 3.93/0.93  --bmc1_pre_inst_next_state              false
% 3.93/0.93  --bmc1_pre_inst_state                   false
% 3.93/0.93  --bmc1_pre_inst_reach_state             false
% 3.93/0.93  --bmc1_out_unsat_core                   false
% 3.93/0.93  --bmc1_aig_witness_out                  false
% 3.93/0.93  --bmc1_verbose                          false
% 3.93/0.93  --bmc1_dump_clauses_tptp                false
% 3.93/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.93/0.93  --bmc1_dump_file                        -
% 3.93/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.93/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.93/0.93  --bmc1_ucm_extend_mode                  1
% 3.93/0.93  --bmc1_ucm_init_mode                    2
% 3.93/0.93  --bmc1_ucm_cone_mode                    none
% 3.93/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.93/0.93  --bmc1_ucm_relax_model                  4
% 3.93/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.93/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.93/0.93  --bmc1_ucm_layered_model                none
% 3.93/0.93  --bmc1_ucm_max_lemma_size               10
% 3.93/0.93  
% 3.93/0.93  ------ AIG Options
% 3.93/0.93  
% 3.93/0.93  --aig_mode                              false
% 3.93/0.93  
% 3.93/0.93  ------ Instantiation Options
% 3.93/0.93  
% 3.93/0.93  --instantiation_flag                    true
% 3.93/0.93  --inst_sos_flag                         true
% 3.93/0.93  --inst_sos_phase                        true
% 3.93/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.93/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.93/0.93  --inst_lit_sel_side                     num_symb
% 3.93/0.93  --inst_solver_per_active                1400
% 3.93/0.93  --inst_solver_calls_frac                1.
% 3.93/0.93  --inst_passive_queue_type               priority_queues
% 3.93/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.93/0.93  --inst_passive_queues_freq              [25;2]
% 3.93/0.93  --inst_dismatching                      true
% 3.93/0.93  --inst_eager_unprocessed_to_passive     true
% 3.93/0.93  --inst_prop_sim_given                   true
% 3.93/0.93  --inst_prop_sim_new                     false
% 3.93/0.93  --inst_subs_new                         false
% 3.93/0.93  --inst_eq_res_simp                      false
% 3.93/0.93  --inst_subs_given                       false
% 3.93/0.93  --inst_orphan_elimination               true
% 3.93/0.93  --inst_learning_loop_flag               true
% 3.93/0.93  --inst_learning_start                   3000
% 3.93/0.93  --inst_learning_factor                  2
% 3.93/0.93  --inst_start_prop_sim_after_learn       3
% 3.93/0.93  --inst_sel_renew                        solver
% 3.93/0.93  --inst_lit_activity_flag                true
% 3.93/0.93  --inst_restr_to_given                   false
% 3.93/0.93  --inst_activity_threshold               500
% 3.93/0.93  --inst_out_proof                        true
% 3.93/0.93  
% 3.93/0.93  ------ Resolution Options
% 3.93/0.93  
% 3.93/0.93  --resolution_flag                       true
% 3.93/0.93  --res_lit_sel                           adaptive
% 3.93/0.93  --res_lit_sel_side                      none
% 3.93/0.93  --res_ordering                          kbo
% 3.93/0.93  --res_to_prop_solver                    active
% 3.93/0.93  --res_prop_simpl_new                    false
% 3.93/0.93  --res_prop_simpl_given                  true
% 3.93/0.93  --res_passive_queue_type                priority_queues
% 3.93/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.93/0.93  --res_passive_queues_freq               [15;5]
% 3.93/0.93  --res_forward_subs                      full
% 3.93/0.93  --res_backward_subs                     full
% 3.93/0.93  --res_forward_subs_resolution           true
% 3.93/0.93  --res_backward_subs_resolution          true
% 3.93/0.93  --res_orphan_elimination                true
% 3.93/0.93  --res_time_limit                        2.
% 3.93/0.93  --res_out_proof                         true
% 3.93/0.93  
% 3.93/0.93  ------ Superposition Options
% 3.93/0.93  
% 3.93/0.93  --superposition_flag                    true
% 3.93/0.93  --sup_passive_queue_type                priority_queues
% 3.93/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.93/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.93/0.93  --demod_completeness_check              fast
% 3.93/0.93  --demod_use_ground                      true
% 3.93/0.93  --sup_to_prop_solver                    passive
% 3.93/0.93  --sup_prop_simpl_new                    true
% 3.93/0.93  --sup_prop_simpl_given                  true
% 3.93/0.93  --sup_fun_splitting                     true
% 3.93/0.93  --sup_smt_interval                      50000
% 3.93/0.93  
% 3.93/0.93  ------ Superposition Simplification Setup
% 3.93/0.93  
% 3.93/0.93  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.93/0.93  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.93/0.93  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.93/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.93/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.93/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.93/0.93  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.93/0.93  --sup_immed_triv                        [TrivRules]
% 3.93/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.93  --sup_immed_bw_main                     []
% 3.93/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.93/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.93/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.93  --sup_input_bw                          []
% 3.93/0.93  
% 3.93/0.93  ------ Combination Options
% 3.93/0.93  
% 3.93/0.93  --comb_res_mult                         3
% 3.93/0.93  --comb_sup_mult                         2
% 3.93/0.93  --comb_inst_mult                        10
% 3.93/0.93  
% 3.93/0.93  ------ Debug Options
% 3.93/0.93  
% 3.93/0.93  --dbg_backtrace                         false
% 3.93/0.93  --dbg_dump_prop_clauses                 false
% 3.93/0.93  --dbg_dump_prop_clauses_file            -
% 3.93/0.93  --dbg_out_stat                          false
% 3.93/0.93  ------ Parsing...
% 3.93/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.93/0.93  
% 3.93/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.93/0.93  
% 3.93/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.93/0.93  
% 3.93/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.93/0.93  ------ Proving...
% 3.93/0.93  ------ Problem Properties 
% 3.93/0.93  
% 3.93/0.93  
% 3.93/0.93  clauses                                 32
% 3.93/0.93  conjectures                             3
% 3.93/0.93  EPR                                     5
% 3.93/0.93  Horn                                    19
% 3.93/0.93  unary                                   8
% 3.93/0.93  binary                                  2
% 3.93/0.93  lits                                    86
% 3.93/0.93  lits eq                                 10
% 3.93/0.93  fd_pure                                 0
% 3.93/0.93  fd_pseudo                               0
% 3.93/0.93  fd_cond                                 5
% 3.93/0.93  fd_pseudo_cond                          2
% 3.93/0.93  AC symbols                              0
% 3.93/0.93  
% 3.93/0.93  ------ Schedule dynamic 5 is on 
% 3.93/0.93  
% 3.93/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.93/0.93  
% 3.93/0.93  
% 3.93/0.93  ------ 
% 3.93/0.93  Current options:
% 3.93/0.93  ------ 
% 3.93/0.93  
% 3.93/0.93  ------ Input Options
% 3.93/0.93  
% 3.93/0.93  --out_options                           all
% 3.93/0.93  --tptp_safe_out                         true
% 3.93/0.93  --problem_path                          ""
% 3.93/0.93  --include_path                          ""
% 3.93/0.93  --clausifier                            res/vclausify_rel
% 3.93/0.93  --clausifier_options                    ""
% 3.93/0.93  --stdin                                 false
% 3.93/0.93  --stats_out                             all
% 3.93/0.93  
% 3.93/0.93  ------ General Options
% 3.93/0.93  
% 3.93/0.93  --fof                                   false
% 3.93/0.93  --time_out_real                         305.
% 3.93/0.93  --time_out_virtual                      -1.
% 3.93/0.93  --symbol_type_check                     false
% 3.93/0.93  --clausify_out                          false
% 3.93/0.93  --sig_cnt_out                           false
% 3.93/0.93  --trig_cnt_out                          false
% 3.93/0.93  --trig_cnt_out_tolerance                1.
% 3.93/0.93  --trig_cnt_out_sk_spl                   false
% 3.93/0.93  --abstr_cl_out                          false
% 3.93/0.93  
% 3.93/0.93  ------ Global Options
% 3.93/0.93  
% 3.93/0.93  --schedule                              default
% 3.93/0.93  --add_important_lit                     false
% 3.93/0.93  --prop_solver_per_cl                    1000
% 3.93/0.93  --min_unsat_core                        false
% 3.93/0.93  --soft_assumptions                      false
% 3.93/0.93  --soft_lemma_size                       3
% 3.93/0.93  --prop_impl_unit_size                   0
% 3.93/0.93  --prop_impl_unit                        []
% 3.93/0.93  --share_sel_clauses                     true
% 3.93/0.93  --reset_solvers                         false
% 3.93/0.93  --bc_imp_inh                            [conj_cone]
% 3.93/0.93  --conj_cone_tolerance                   3.
% 3.93/0.93  --extra_neg_conj                        none
% 3.93/0.93  --large_theory_mode                     true
% 3.93/0.93  --prolific_symb_bound                   200
% 3.93/0.93  --lt_threshold                          2000
% 3.93/0.93  --clause_weak_htbl                      true
% 3.93/0.93  --gc_record_bc_elim                     false
% 3.93/0.93  
% 3.93/0.93  ------ Preprocessing Options
% 3.93/0.93  
% 3.93/0.93  --preprocessing_flag                    true
% 3.93/0.93  --time_out_prep_mult                    0.1
% 3.93/0.93  --splitting_mode                        input
% 3.93/0.93  --splitting_grd                         true
% 3.93/0.93  --splitting_cvd                         false
% 3.93/0.93  --splitting_cvd_svl                     false
% 3.93/0.93  --splitting_nvd                         32
% 3.93/0.93  --sub_typing                            true
% 3.93/0.93  --prep_gs_sim                           true
% 3.93/0.93  --prep_unflatten                        true
% 3.93/0.93  --prep_res_sim                          true
% 3.93/0.93  --prep_upred                            true
% 3.93/0.93  --prep_sem_filter                       exhaustive
% 3.93/0.93  --prep_sem_filter_out                   false
% 3.93/0.93  --pred_elim                             true
% 3.93/0.93  --res_sim_input                         true
% 3.93/0.93  --eq_ax_congr_red                       true
% 3.93/0.93  --pure_diseq_elim                       true
% 3.93/0.93  --brand_transform                       false
% 3.93/0.93  --non_eq_to_eq                          false
% 3.93/0.93  --prep_def_merge                        true
% 3.93/0.93  --prep_def_merge_prop_impl              false
% 3.93/0.93  --prep_def_merge_mbd                    true
% 3.93/0.93  --prep_def_merge_tr_red                 false
% 3.93/0.93  --prep_def_merge_tr_cl                  false
% 3.93/0.93  --smt_preprocessing                     true
% 3.93/0.93  --smt_ac_axioms                         fast
% 3.93/0.93  --preprocessed_out                      false
% 3.93/0.93  --preprocessed_stats                    false
% 3.93/0.93  
% 3.93/0.93  ------ Abstraction refinement Options
% 3.93/0.93  
% 3.93/0.93  --abstr_ref                             []
% 3.93/0.93  --abstr_ref_prep                        false
% 3.93/0.93  --abstr_ref_until_sat                   false
% 3.93/0.93  --abstr_ref_sig_restrict                funpre
% 3.93/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.93/0.93  --abstr_ref_under                       []
% 3.93/0.93  
% 3.93/0.93  ------ SAT Options
% 3.93/0.93  
% 3.93/0.93  --sat_mode                              false
% 3.93/0.93  --sat_fm_restart_options                ""
% 3.93/0.93  --sat_gr_def                            false
% 3.93/0.93  --sat_epr_types                         true
% 3.93/0.93  --sat_non_cyclic_types                  false
% 3.93/0.93  --sat_finite_models                     false
% 3.93/0.93  --sat_fm_lemmas                         false
% 3.93/0.93  --sat_fm_prep                           false
% 3.93/0.93  --sat_fm_uc_incr                        true
% 3.93/0.93  --sat_out_model                         small
% 3.93/0.93  --sat_out_clauses                       false
% 3.93/0.93  
% 3.93/0.93  ------ QBF Options
% 3.93/0.93  
% 3.93/0.93  --qbf_mode                              false
% 3.93/0.93  --qbf_elim_univ                         false
% 3.93/0.93  --qbf_dom_inst                          none
% 3.93/0.93  --qbf_dom_pre_inst                      false
% 3.93/0.93  --qbf_sk_in                             false
% 3.93/0.93  --qbf_pred_elim                         true
% 3.93/0.93  --qbf_split                             512
% 3.93/0.93  
% 3.93/0.93  ------ BMC1 Options
% 3.93/0.93  
% 3.93/0.93  --bmc1_incremental                      false
% 3.93/0.93  --bmc1_axioms                           reachable_all
% 3.93/0.93  --bmc1_min_bound                        0
% 3.93/0.93  --bmc1_max_bound                        -1
% 3.93/0.93  --bmc1_max_bound_default                -1
% 3.93/0.93  --bmc1_symbol_reachability              true
% 3.93/0.93  --bmc1_property_lemmas                  false
% 3.93/0.93  --bmc1_k_induction                      false
% 3.93/0.93  --bmc1_non_equiv_states                 false
% 3.93/0.93  --bmc1_deadlock                         false
% 3.93/0.93  --bmc1_ucm                              false
% 3.93/0.93  --bmc1_add_unsat_core                   none
% 3.93/0.93  --bmc1_unsat_core_children              false
% 3.93/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.93/0.93  --bmc1_out_stat                         full
% 3.93/0.93  --bmc1_ground_init                      false
% 3.93/0.93  --bmc1_pre_inst_next_state              false
% 3.93/0.93  --bmc1_pre_inst_state                   false
% 3.93/0.93  --bmc1_pre_inst_reach_state             false
% 3.93/0.93  --bmc1_out_unsat_core                   false
% 3.93/0.93  --bmc1_aig_witness_out                  false
% 3.93/0.93  --bmc1_verbose                          false
% 3.93/0.93  --bmc1_dump_clauses_tptp                false
% 3.93/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.93/0.93  --bmc1_dump_file                        -
% 3.93/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.93/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.93/0.93  --bmc1_ucm_extend_mode                  1
% 3.93/0.93  --bmc1_ucm_init_mode                    2
% 3.93/0.93  --bmc1_ucm_cone_mode                    none
% 3.93/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.93/0.93  --bmc1_ucm_relax_model                  4
% 3.93/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.93/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.93/0.93  --bmc1_ucm_layered_model                none
% 3.93/0.93  --bmc1_ucm_max_lemma_size               10
% 3.93/0.93  
% 3.93/0.93  ------ AIG Options
% 3.93/0.93  
% 3.93/0.93  --aig_mode                              false
% 3.93/0.93  
% 3.93/0.93  ------ Instantiation Options
% 3.93/0.93  
% 3.93/0.93  --instantiation_flag                    true
% 3.93/0.93  --inst_sos_flag                         true
% 3.93/0.93  --inst_sos_phase                        true
% 3.93/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.93/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.93/0.93  --inst_lit_sel_side                     none
% 3.93/0.93  --inst_solver_per_active                1400
% 3.93/0.93  --inst_solver_calls_frac                1.
% 3.93/0.93  --inst_passive_queue_type               priority_queues
% 3.93/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.93/0.93  --inst_passive_queues_freq              [25;2]
% 3.93/0.93  --inst_dismatching                      true
% 3.93/0.93  --inst_eager_unprocessed_to_passive     true
% 3.93/0.93  --inst_prop_sim_given                   true
% 3.93/0.93  --inst_prop_sim_new                     false
% 3.93/0.93  --inst_subs_new                         false
% 3.93/0.93  --inst_eq_res_simp                      false
% 3.93/0.93  --inst_subs_given                       false
% 3.93/0.93  --inst_orphan_elimination               true
% 3.93/0.93  --inst_learning_loop_flag               true
% 3.93/0.93  --inst_learning_start                   3000
% 3.93/0.93  --inst_learning_factor                  2
% 3.93/0.93  --inst_start_prop_sim_after_learn       3
% 3.93/0.93  --inst_sel_renew                        solver
% 3.93/0.93  --inst_lit_activity_flag                true
% 3.93/0.93  --inst_restr_to_given                   false
% 3.93/0.93  --inst_activity_threshold               500
% 3.93/0.93  --inst_out_proof                        true
% 3.93/0.93  
% 3.93/0.93  ------ Resolution Options
% 3.93/0.93  
% 3.93/0.93  --resolution_flag                       false
% 3.93/0.93  --res_lit_sel                           adaptive
% 3.93/0.93  --res_lit_sel_side                      none
% 3.93/0.93  --res_ordering                          kbo
% 3.93/0.93  --res_to_prop_solver                    active
% 3.93/0.93  --res_prop_simpl_new                    false
% 3.93/0.93  --res_prop_simpl_given                  true
% 3.93/0.93  --res_passive_queue_type                priority_queues
% 3.93/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.93/0.93  --res_passive_queues_freq               [15;5]
% 3.93/0.93  --res_forward_subs                      full
% 3.93/0.93  --res_backward_subs                     full
% 3.93/0.93  --res_forward_subs_resolution           true
% 3.93/0.93  --res_backward_subs_resolution          true
% 3.93/0.93  --res_orphan_elimination                true
% 3.93/0.93  --res_time_limit                        2.
% 3.93/0.93  --res_out_proof                         true
% 3.93/0.93  
% 3.93/0.93  ------ Superposition Options
% 3.93/0.93  
% 3.93/0.93  --superposition_flag                    true
% 3.93/0.93  --sup_passive_queue_type                priority_queues
% 3.93/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.93/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.93/0.93  --demod_completeness_check              fast
% 3.93/0.93  --demod_use_ground                      true
% 3.93/0.93  --sup_to_prop_solver                    passive
% 3.93/0.93  --sup_prop_simpl_new                    true
% 3.93/0.93  --sup_prop_simpl_given                  true
% 3.93/0.93  --sup_fun_splitting                     true
% 3.93/0.93  --sup_smt_interval                      50000
% 3.93/0.93  
% 3.93/0.93  ------ Superposition Simplification Setup
% 3.93/0.93  
% 3.93/0.93  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.93/0.93  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.93/0.93  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.93/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.93/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.93/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.93/0.93  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.93/0.93  --sup_immed_triv                        [TrivRules]
% 3.93/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.93  --sup_immed_bw_main                     []
% 3.93/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.93/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.93/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.93  --sup_input_bw                          []
% 3.93/0.93  
% 3.93/0.93  ------ Combination Options
% 3.93/0.93  
% 3.93/0.93  --comb_res_mult                         3
% 3.93/0.93  --comb_sup_mult                         2
% 3.93/0.93  --comb_inst_mult                        10
% 3.93/0.93  
% 3.93/0.93  ------ Debug Options
% 3.93/0.93  
% 3.93/0.93  --dbg_backtrace                         false
% 3.93/0.93  --dbg_dump_prop_clauses                 false
% 3.93/0.93  --dbg_dump_prop_clauses_file            -
% 3.93/0.93  --dbg_out_stat                          false
% 3.93/0.93  
% 3.93/0.93  
% 3.93/0.93  
% 3.93/0.93  
% 3.93/0.93  ------ Proving...
% 3.93/0.93  
% 3.93/0.93  
% 3.93/0.93  % SZS status Theorem for theBenchmark.p
% 3.93/0.93  
% 3.93/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 3.93/0.93  
% 3.93/0.93  fof(f4,axiom,(
% 3.93/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 3.93/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.93  
% 3.93/0.93  fof(f24,plain,(
% 3.93/0.93    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.93/0.93    inference(ennf_transformation,[],[f4])).
% 3.93/0.93  
% 3.93/0.93  fof(f25,plain,(
% 3.93/0.93    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.93/0.93    inference(flattening,[],[f24])).
% 3.93/0.93  
% 3.93/0.93  fof(f47,plain,(
% 3.93/0.93    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),X0)))),
% 3.93/0.93    introduced(choice_axiom,[])).
% 3.93/0.93  
% 3.93/0.93  fof(f48,plain,(
% 3.93/0.93    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.93/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f47])).
% 3.93/0.93  
% 3.93/0.93  fof(f73,plain,(
% 3.93/0.93    ( ! [X0,X1] : (X0 = X1 | m1_subset_1(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.93/0.93    inference(cnf_transformation,[],[f48])).
% 3.93/0.93  
% 3.93/0.93  fof(f9,axiom,(
% 3.93/0.93    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 3.93/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.93  
% 3.93/0.93  fof(f32,plain,(
% 3.93/0.93    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.93/0.93    inference(ennf_transformation,[],[f9])).
% 3.93/0.93  
% 3.93/0.93  fof(f33,plain,(
% 3.93/0.93    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.93/0.93    inference(flattening,[],[f32])).
% 3.93/0.93  
% 3.93/0.93  fof(f49,plain,(
% 3.93/0.93    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.93/0.93    inference(nnf_transformation,[],[f33])).
% 3.93/0.93  
% 3.93/0.93  fof(f50,plain,(
% 3.93/0.93    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.93/0.93    inference(rectify,[],[f49])).
% 3.93/0.93  
% 3.93/0.93  fof(f51,plain,(
% 3.93/0.93    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 3.93/0.93    introduced(choice_axiom,[])).
% 3.93/0.93  
% 3.93/0.93  fof(f52,plain,(
% 3.93/0.93    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.93/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).
% 3.93/0.93  
% 3.93/0.93  fof(f81,plain,(
% 3.93/0.93    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.93/0.93    inference(cnf_transformation,[],[f52])).
% 3.93/0.93  
% 3.93/0.93  fof(f16,conjecture,(
% 3.93/0.93    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.93/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.93  
% 3.93/0.93  fof(f17,negated_conjecture,(
% 3.93/0.93    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.93/0.93    inference(negated_conjecture,[],[f16])).
% 3.93/0.93  
% 3.93/0.93  fof(f18,plain,(
% 3.93/0.93    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.93/0.93    inference(pure_predicate_removal,[],[f17])).
% 3.93/0.93  
% 3.93/0.93  fof(f19,plain,(
% 3.93/0.93    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.93/0.93    inference(pure_predicate_removal,[],[f18])).
% 3.93/0.93  
% 3.93/0.93  fof(f20,plain,(
% 3.93/0.93    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.93/0.93    inference(pure_predicate_removal,[],[f19])).
% 3.93/0.93  
% 3.93/0.93  fof(f43,plain,(
% 3.93/0.93    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.93/0.93    inference(ennf_transformation,[],[f20])).
% 3.93/0.93  
% 3.93/0.93  fof(f44,plain,(
% 3.93/0.93    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.93/0.93    inference(flattening,[],[f43])).
% 3.93/0.93  
% 3.93/0.93  fof(f64,plain,(
% 3.93/0.93    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.93/0.93    inference(nnf_transformation,[],[f44])).
% 3.93/0.93  
% 3.93/0.93  fof(f65,plain,(
% 3.93/0.93    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.93/0.93    inference(flattening,[],[f64])).
% 3.93/0.93  
% 3.93/0.93  fof(f67,plain,(
% 3.93/0.93    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK7) | ~v1_subset_1(sK7,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK7) | v1_subset_1(sK7,u1_struct_0(X0))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK7,X0) & ~v1_xboole_0(sK7))) )),
% 3.93/0.93    introduced(choice_axiom,[])).
% 3.93/0.93  
% 3.93/0.93  fof(f66,plain,(
% 3.93/0.93    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK6),X1) | ~v1_subset_1(X1,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),X1) | v1_subset_1(X1,u1_struct_0(sK6))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(X1,sK6) & ~v1_xboole_0(X1)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & ~v2_struct_0(sK6))),
% 3.93/0.93    introduced(choice_axiom,[])).
% 3.93/0.93  
% 3.93/0.93  fof(f68,plain,(
% 3.93/0.93    ((r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(sK7,sK6) & ~v1_xboole_0(sK7)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & ~v2_struct_0(sK6)),
% 3.93/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f65,f67,f66])).
% 3.93/0.93  
% 3.93/0.93  fof(f102,plain,(
% 3.93/0.93    l1_orders_2(sK6)),
% 3.93/0.93    inference(cnf_transformation,[],[f68])).
% 3.93/0.93  
% 3.93/0.93  fof(f80,plain,(
% 3.93/0.93    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.93/0.93    inference(cnf_transformation,[],[f52])).
% 3.93/0.93  
% 3.93/0.93  fof(f79,plain,(
% 3.93/0.93    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.93/0.93    inference(cnf_transformation,[],[f52])).
% 3.93/0.93  
% 3.93/0.93  fof(f105,plain,(
% 3.93/0.93    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 3.93/0.93    inference(cnf_transformation,[],[f68])).
% 3.93/0.93  
% 3.93/0.93  fof(f14,axiom,(
% 3.93/0.93    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 3.93/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.93  
% 3.93/0.93  fof(f40,plain,(
% 3.93/0.93    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.93/0.93    inference(ennf_transformation,[],[f14])).
% 3.93/0.93  
% 3.93/0.93  fof(f41,plain,(
% 3.93/0.93    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.93/0.93    inference(flattening,[],[f40])).
% 3.93/0.93  
% 3.93/0.93  fof(f58,plain,(
% 3.93/0.93    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.93/0.93    inference(nnf_transformation,[],[f41])).
% 3.93/0.93  
% 3.93/0.93  fof(f59,plain,(
% 3.93/0.93    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.93/0.93    inference(rectify,[],[f58])).
% 3.93/0.93  
% 3.93/0.93  fof(f61,plain,(
% 3.93/0.93    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,X2,sK5(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))) )),
% 3.93/0.93    introduced(choice_axiom,[])).
% 3.93/0.93  
% 3.93/0.93  fof(f60,plain,(
% 3.93/0.93    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 3.93/0.93    introduced(choice_axiom,[])).
% 3.93/0.93  
% 3.93/0.93  fof(f62,plain,(
% 3.93/0.93    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.93/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f59,f61,f60])).
% 3.93/0.93  
% 3.93/0.93  fof(f91,plain,(
% 3.93/0.93    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.93/0.93    inference(cnf_transformation,[],[f62])).
% 3.93/0.93  
% 3.93/0.93  fof(f7,axiom,(
% 3.93/0.93    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.93/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.93  
% 3.93/0.93  fof(f29,plain,(
% 3.93/0.93    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.93/0.93    inference(ennf_transformation,[],[f7])).
% 3.93/0.93  
% 3.93/0.93  fof(f30,plain,(
% 3.93/0.93    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.93/0.93    inference(flattening,[],[f29])).
% 3.93/0.93  
% 3.93/0.93  fof(f77,plain,(
% 3.93/0.93    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.93/0.93    inference(cnf_transformation,[],[f30])).
% 3.93/0.93  
% 3.93/0.93  fof(f104,plain,(
% 3.93/0.93    v13_waybel_0(sK7,sK6)),
% 3.93/0.93    inference(cnf_transformation,[],[f68])).
% 3.93/0.93  
% 3.93/0.93  fof(f1,axiom,(
% 3.93/0.93    v1_xboole_0(k1_xboole_0)),
% 3.93/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.93  
% 3.93/0.93  fof(f69,plain,(
% 3.93/0.93    v1_xboole_0(k1_xboole_0)),
% 3.93/0.93    inference(cnf_transformation,[],[f1])).
% 3.93/0.93  
% 3.93/0.93  fof(f11,axiom,(
% 3.93/0.93    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 3.93/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.93  
% 3.93/0.93  fof(f35,plain,(
% 3.93/0.93    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.93/0.93    inference(ennf_transformation,[],[f11])).
% 3.93/0.93  
% 3.93/0.93  fof(f36,plain,(
% 3.93/0.93    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.93/0.93    inference(flattening,[],[f35])).
% 3.93/0.93  
% 3.93/0.93  fof(f53,plain,(
% 3.93/0.93    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.93/0.93    inference(nnf_transformation,[],[f36])).
% 3.93/0.93  
% 3.93/0.93  fof(f54,plain,(
% 3.93/0.93    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.93/0.93    inference(flattening,[],[f53])).
% 3.93/0.93  
% 3.93/0.93  fof(f55,plain,(
% 3.93/0.93    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.93/0.93    inference(rectify,[],[f54])).
% 3.93/0.93  
% 3.93/0.93  fof(f56,plain,(
% 3.93/0.93    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) & r2_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 3.93/0.93    introduced(choice_axiom,[])).
% 3.93/0.93  
% 3.93/0.93  fof(f57,plain,(
% 3.93/0.93    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) & r2_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.93/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).
% 3.93/0.93  
% 3.93/0.93  fof(f85,plain,(
% 3.93/0.93    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.93/0.93    inference(cnf_transformation,[],[f57])).
% 3.93/0.93  
% 3.93/0.93  fof(f108,plain,(
% 3.93/0.93    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.93/0.93    inference(equality_resolution,[],[f85])).
% 3.93/0.93  
% 3.93/0.93  fof(f12,axiom,(
% 3.93/0.93    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 3.93/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.93  
% 3.93/0.93  fof(f37,plain,(
% 3.93/0.93    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.93/0.93    inference(ennf_transformation,[],[f12])).
% 3.93/0.93  
% 3.93/0.93  fof(f89,plain,(
% 3.93/0.93    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.93/0.93    inference(cnf_transformation,[],[f37])).
% 3.93/0.93  
% 3.93/0.93  fof(f13,axiom,(
% 3.93/0.93    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 3.93/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.93  
% 3.93/0.93  fof(f21,plain,(
% 3.93/0.93    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 3.93/0.93    inference(pure_predicate_removal,[],[f13])).
% 3.93/0.93  
% 3.93/0.93  fof(f38,plain,(
% 3.93/0.93    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.93/0.93    inference(ennf_transformation,[],[f21])).
% 3.93/0.93  
% 3.93/0.93  fof(f39,plain,(
% 3.93/0.93    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.93/0.93    inference(flattening,[],[f38])).
% 3.93/0.93  
% 3.93/0.93  fof(f90,plain,(
% 3.93/0.93    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.93/0.93    inference(cnf_transformation,[],[f39])).
% 3.93/0.93  
% 3.93/0.93  fof(f101,plain,(
% 3.93/0.93    v1_yellow_0(sK6)),
% 3.93/0.93    inference(cnf_transformation,[],[f68])).
% 3.93/0.93  
% 3.93/0.93  fof(f99,plain,(
% 3.93/0.93    ~v2_struct_0(sK6)),
% 3.93/0.93    inference(cnf_transformation,[],[f68])).
% 3.93/0.93  
% 3.93/0.93  fof(f100,plain,(
% 3.93/0.93    v5_orders_2(sK6)),
% 3.93/0.93    inference(cnf_transformation,[],[f68])).
% 3.93/0.93  
% 3.93/0.93  fof(f10,axiom,(
% 3.93/0.93    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 3.93/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.93  
% 3.93/0.93  fof(f34,plain,(
% 3.93/0.93    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 3.93/0.93    inference(ennf_transformation,[],[f10])).
% 3.93/0.93  
% 3.93/0.93  fof(f83,plain,(
% 3.93/0.93    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 3.93/0.93    inference(cnf_transformation,[],[f34])).
% 3.93/0.93  
% 3.93/0.93  fof(f2,axiom,(
% 3.93/0.93    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.93/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.93  
% 3.93/0.93  fof(f70,plain,(
% 3.93/0.93    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.93/0.93    inference(cnf_transformation,[],[f2])).
% 3.93/0.93  
% 3.93/0.93  fof(f3,axiom,(
% 3.93/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 3.93/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.93  
% 3.93/0.93  fof(f22,plain,(
% 3.93/0.93    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.93/0.93    inference(ennf_transformation,[],[f3])).
% 3.93/0.93  
% 3.93/0.93  fof(f23,plain,(
% 3.93/0.93    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.93/0.93    inference(flattening,[],[f22])).
% 3.93/0.93  
% 3.93/0.93  fof(f45,plain,(
% 3.93/0.93    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)))),
% 3.93/0.93    introduced(choice_axiom,[])).
% 3.93/0.93  
% 3.93/0.93  fof(f46,plain,(
% 3.93/0.93    ! [X0,X1] : ((r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.93/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f45])).
% 3.93/0.93  
% 3.93/0.93  fof(f72,plain,(
% 3.93/0.93    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.93/0.93    inference(cnf_transformation,[],[f46])).
% 3.93/0.93  
% 3.93/0.93  fof(f8,axiom,(
% 3.93/0.93    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.93/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.93  
% 3.93/0.93  fof(f31,plain,(
% 3.93/0.93    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.93/0.93    inference(ennf_transformation,[],[f8])).
% 3.93/0.93  
% 3.93/0.93  fof(f78,plain,(
% 3.93/0.93    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.93/0.93    inference(cnf_transformation,[],[f31])).
% 3.93/0.93  
% 3.93/0.93  fof(f84,plain,(
% 3.93/0.93    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.93/0.93    inference(cnf_transformation,[],[f57])).
% 3.93/0.93  
% 3.93/0.93  fof(f109,plain,(
% 3.93/0.93    ( ! [X0,X1] : (r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.93/0.93    inference(equality_resolution,[],[f84])).
% 3.93/0.93  
% 3.93/0.93  fof(f103,plain,(
% 3.93/0.93    ~v1_xboole_0(sK7)),
% 3.93/0.93    inference(cnf_transformation,[],[f68])).
% 3.93/0.93  
% 3.93/0.93  fof(f15,axiom,(
% 3.93/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.93/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.93  
% 3.93/0.93  fof(f42,plain,(
% 3.93/0.93    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.93/0.93    inference(ennf_transformation,[],[f15])).
% 3.93/0.93  
% 3.93/0.93  fof(f63,plain,(
% 3.93/0.93    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.93/0.93    inference(nnf_transformation,[],[f42])).
% 3.93/0.93  
% 3.93/0.93  fof(f98,plain,(
% 3.93/0.93    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.93/0.93    inference(cnf_transformation,[],[f63])).
% 3.93/0.93  
% 3.93/0.93  fof(f107,plain,(
% 3.93/0.93    r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))),
% 3.93/0.93    inference(cnf_transformation,[],[f68])).
% 3.93/0.93  
% 3.93/0.93  fof(f6,axiom,(
% 3.93/0.93    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.93/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/0.93  
% 3.93/0.93  fof(f27,plain,(
% 3.93/0.93    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.93/0.93    inference(ennf_transformation,[],[f6])).
% 3.93/0.93  
% 3.93/0.93  fof(f28,plain,(
% 3.93/0.93    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.93/0.93    inference(flattening,[],[f27])).
% 3.93/0.93  
% 3.93/0.93  fof(f76,plain,(
% 3.93/0.93    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.93/0.93    inference(cnf_transformation,[],[f28])).
% 3.93/0.93  
% 3.93/0.93  fof(f74,plain,(
% 3.93/0.93    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.93/0.93    inference(cnf_transformation,[],[f48])).
% 3.93/0.93  
% 3.93/0.93  fof(f97,plain,(
% 3.93/0.93    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.93/0.93    inference(cnf_transformation,[],[f63])).
% 3.93/0.93  
% 3.93/0.93  fof(f110,plain,(
% 3.93/0.93    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 3.93/0.93    inference(equality_resolution,[],[f97])).
% 3.93/0.93  
% 3.93/0.93  fof(f106,plain,(
% 3.93/0.93    ~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))),
% 3.93/0.93    inference(cnf_transformation,[],[f68])).
% 3.93/0.93  
% 3.93/0.93  cnf(c_5,plain,
% 3.93/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.93/0.93      | m1_subset_1(sK1(X1,X0),X1)
% 3.93/0.93      | X0 = X1 ),
% 3.93/0.93      inference(cnf_transformation,[],[f73]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2572,plain,
% 3.93/0.93      ( X0 = X1
% 3.93/0.93      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.93/0.93      | m1_subset_1(sK1(X1,X0),X1) = iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_11,plain,
% 3.93/0.93      ( r2_lattice3(X0,X1,X2)
% 3.93/0.93      | r2_hidden(sK2(X0,X1,X2),X1)
% 3.93/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.93/0.93      | ~ l1_orders_2(X0) ),
% 3.93/0.93      inference(cnf_transformation,[],[f81]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_35,negated_conjecture,
% 3.93/0.93      ( l1_orders_2(sK6) ),
% 3.93/0.93      inference(cnf_transformation,[],[f102]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_843,plain,
% 3.93/0.93      ( r2_lattice3(X0,X1,X2)
% 3.93/0.93      | r2_hidden(sK2(X0,X1,X2),X1)
% 3.93/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.93/0.93      | sK6 != X0 ),
% 3.93/0.93      inference(resolution_lifted,[status(thm)],[c_11,c_35]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_844,plain,
% 3.93/0.93      ( r2_lattice3(sK6,X0,X1)
% 3.93/0.93      | r2_hidden(sK2(sK6,X0,X1),X0)
% 3.93/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
% 3.93/0.93      inference(unflattening,[status(thm)],[c_843]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2552,plain,
% 3.93/0.93      ( r2_lattice3(sK6,X0,X1) = iProver_top
% 3.93/0.93      | r2_hidden(sK2(sK6,X0,X1),X0) = iProver_top
% 3.93/0.93      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_844]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_12,plain,
% 3.93/0.93      ( r2_lattice3(X0,X1,X2)
% 3.93/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.93/0.93      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 3.93/0.93      | ~ l1_orders_2(X0) ),
% 3.93/0.93      inference(cnf_transformation,[],[f80]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_828,plain,
% 3.93/0.93      ( r2_lattice3(X0,X1,X2)
% 3.93/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.93/0.93      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 3.93/0.93      | sK6 != X0 ),
% 3.93/0.93      inference(resolution_lifted,[status(thm)],[c_12,c_35]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_829,plain,
% 3.93/0.93      ( r2_lattice3(sK6,X0,X1)
% 3.93/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.93/0.93      | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6)) ),
% 3.93/0.93      inference(unflattening,[status(thm)],[c_828]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2553,plain,
% 3.93/0.93      ( r2_lattice3(sK6,X0,X1) = iProver_top
% 3.93/0.93      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.93/0.93      | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6)) = iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_829]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_13,plain,
% 3.93/0.93      ( r1_orders_2(X0,X1,X2)
% 3.93/0.93      | ~ r2_lattice3(X0,X3,X2)
% 3.93/0.93      | ~ r2_hidden(X1,X3)
% 3.93/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.93/0.93      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.93/0.93      | ~ l1_orders_2(X0) ),
% 3.93/0.93      inference(cnf_transformation,[],[f79]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_807,plain,
% 3.93/0.93      ( r1_orders_2(X0,X1,X2)
% 3.93/0.93      | ~ r2_lattice3(X0,X3,X2)
% 3.93/0.93      | ~ r2_hidden(X1,X3)
% 3.93/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.93/0.93      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.93/0.93      | sK6 != X0 ),
% 3.93/0.93      inference(resolution_lifted,[status(thm)],[c_13,c_35]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_808,plain,
% 3.93/0.93      ( r1_orders_2(sK6,X0,X1)
% 3.93/0.93      | ~ r2_lattice3(sK6,X2,X1)
% 3.93/0.93      | ~ r2_hidden(X0,X2)
% 3.93/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.93/0.93      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 3.93/0.93      inference(unflattening,[status(thm)],[c_807]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2554,plain,
% 3.93/0.93      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 3.93/0.93      | r2_lattice3(sK6,X2,X1) != iProver_top
% 3.93/0.93      | r2_hidden(X0,X2) != iProver_top
% 3.93/0.93      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.93/0.93      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_808]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_3744,plain,
% 3.93/0.93      ( r1_orders_2(sK6,sK2(sK6,X0,X1),X2) = iProver_top
% 3.93/0.93      | r2_lattice3(sK6,X3,X2) != iProver_top
% 3.93/0.93      | r2_lattice3(sK6,X0,X1) = iProver_top
% 3.93/0.93      | r2_hidden(sK2(sK6,X0,X1),X3) != iProver_top
% 3.93/0.93      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.93/0.93      | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_2553,c_2554]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_7669,plain,
% 3.93/0.93      ( r1_orders_2(sK6,sK2(sK6,X0,X1),X2) = iProver_top
% 3.93/0.93      | r2_lattice3(sK6,X0,X2) != iProver_top
% 3.93/0.93      | r2_lattice3(sK6,X0,X1) = iProver_top
% 3.93/0.93      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.93/0.93      | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_2552,c_3744]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_32,negated_conjecture,
% 3.93/0.93      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.93/0.93      inference(cnf_transformation,[],[f105]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2567,plain,
% 3.93/0.93      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_27,plain,
% 3.93/0.93      ( ~ r1_orders_2(X0,X1,X2)
% 3.93/0.93      | ~ v13_waybel_0(X3,X0)
% 3.93/0.93      | ~ r2_hidden(X1,X3)
% 3.93/0.93      | r2_hidden(X2,X3)
% 3.93/0.93      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.93/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.93/0.93      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.93/0.93      | ~ l1_orders_2(X0) ),
% 3.93/0.93      inference(cnf_transformation,[],[f91]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_753,plain,
% 3.93/0.93      ( ~ r1_orders_2(X0,X1,X2)
% 3.93/0.93      | ~ v13_waybel_0(X3,X0)
% 3.93/0.93      | ~ r2_hidden(X1,X3)
% 3.93/0.93      | r2_hidden(X2,X3)
% 3.93/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.93/0.93      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.93/0.93      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.93/0.93      | sK6 != X0 ),
% 3.93/0.93      inference(resolution_lifted,[status(thm)],[c_27,c_35]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_754,plain,
% 3.93/0.93      ( ~ r1_orders_2(sK6,X0,X1)
% 3.93/0.93      | ~ v13_waybel_0(X2,sK6)
% 3.93/0.93      | ~ r2_hidden(X0,X2)
% 3.93/0.93      | r2_hidden(X1,X2)
% 3.93/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.93/0.93      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.93/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.93/0.93      inference(unflattening,[status(thm)],[c_753]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_8,plain,
% 3.93/0.93      ( ~ r2_hidden(X0,X1)
% 3.93/0.93      | m1_subset_1(X0,X2)
% 3.93/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.93/0.93      inference(cnf_transformation,[],[f77]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_770,plain,
% 3.93/0.93      ( ~ r1_orders_2(sK6,X0,X1)
% 3.93/0.93      | ~ v13_waybel_0(X2,sK6)
% 3.93/0.93      | ~ r2_hidden(X0,X2)
% 3.93/0.93      | r2_hidden(X1,X2)
% 3.93/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.93/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.93/0.93      inference(forward_subsumption_resolution,[status(thm)],[c_754,c_8]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2557,plain,
% 3.93/0.93      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.93/0.93      | v13_waybel_0(X2,sK6) != iProver_top
% 3.93/0.93      | r2_hidden(X0,X2) != iProver_top
% 3.93/0.93      | r2_hidden(X1,X2) = iProver_top
% 3.93/0.93      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.93/0.93      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_770]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_4186,plain,
% 3.93/0.93      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.93/0.93      | v13_waybel_0(sK7,sK6) != iProver_top
% 3.93/0.93      | r2_hidden(X0,sK7) != iProver_top
% 3.93/0.93      | r2_hidden(X1,sK7) = iProver_top
% 3.93/0.93      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_2567,c_2557]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_45,plain,
% 3.93/0.93      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_33,negated_conjecture,
% 3.93/0.93      ( v13_waybel_0(sK7,sK6) ),
% 3.93/0.93      inference(cnf_transformation,[],[f104]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_981,plain,
% 3.93/0.93      ( ~ r1_orders_2(sK6,X0,X1)
% 3.93/0.93      | ~ r2_hidden(X0,X2)
% 3.93/0.93      | r2_hidden(X1,X2)
% 3.93/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.93/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.93/0.93      | sK7 != X2
% 3.93/0.93      | sK6 != sK6 ),
% 3.93/0.93      inference(resolution_lifted,[status(thm)],[c_33,c_770]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_982,plain,
% 3.93/0.93      ( ~ r1_orders_2(sK6,X0,X1)
% 3.93/0.93      | ~ r2_hidden(X0,sK7)
% 3.93/0.93      | r2_hidden(X1,sK7)
% 3.93/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.93/0.93      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.93/0.93      inference(unflattening,[status(thm)],[c_981]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_983,plain,
% 3.93/0.93      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.93/0.93      | r2_hidden(X0,sK7) != iProver_top
% 3.93/0.93      | r2_hidden(X1,sK7) = iProver_top
% 3.93/0.93      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.93/0.93      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_982]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_4364,plain,
% 3.93/0.93      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.93/0.93      | r2_hidden(X0,sK7) != iProver_top
% 3.93/0.93      | r2_hidden(X1,sK7) = iProver_top
% 3.93/0.93      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 3.93/0.93      inference(global_propositional_subsumption,
% 3.93/0.93                [status(thm)],
% 3.93/0.93                [c_4186,c_45,c_983]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_8034,plain,
% 3.93/0.93      ( r2_lattice3(sK6,X0,X1) != iProver_top
% 3.93/0.93      | r2_lattice3(sK6,X0,X2) = iProver_top
% 3.93/0.93      | r2_hidden(X1,sK7) = iProver_top
% 3.93/0.93      | r2_hidden(sK2(sK6,X0,X2),sK7) != iProver_top
% 3.93/0.93      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.93/0.93      | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_7669,c_4364]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_8041,plain,
% 3.93/0.93      ( r2_lattice3(sK6,sK7,X0) != iProver_top
% 3.93/0.93      | r2_lattice3(sK6,sK7,X1) = iProver_top
% 3.93/0.93      | r2_hidden(X0,sK7) = iProver_top
% 3.93/0.93      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.93/0.93      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_2552,c_8034]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_0,plain,
% 3.93/0.93      ( v1_xboole_0(k1_xboole_0) ),
% 3.93/0.93      inference(cnf_transformation,[],[f69]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_133,plain,
% 3.93/0.93      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_18,plain,
% 3.93/0.93      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.93/0.93      | ~ r2_lattice3(X0,X1,X2)
% 3.93/0.93      | ~ r1_yellow_0(X0,X1)
% 3.93/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.93/0.93      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.93/0.93      | ~ l1_orders_2(X0) ),
% 3.93/0.93      inference(cnf_transformation,[],[f108]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_20,plain,
% 3.93/0.93      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.93/0.93      | ~ l1_orders_2(X0) ),
% 3.93/0.93      inference(cnf_transformation,[],[f89]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_239,plain,
% 3.93/0.93      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.93/0.93      | ~ r1_yellow_0(X0,X1)
% 3.93/0.93      | ~ r2_lattice3(X0,X1,X2)
% 3.93/0.93      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.93/0.93      | ~ l1_orders_2(X0) ),
% 3.93/0.93      inference(global_propositional_subsumption,
% 3.93/0.93                [status(thm)],
% 3.93/0.93                [c_18,c_20]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_240,plain,
% 3.93/0.93      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.93/0.93      | ~ r2_lattice3(X0,X1,X2)
% 3.93/0.93      | ~ r1_yellow_0(X0,X1)
% 3.93/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.93/0.93      | ~ l1_orders_2(X0) ),
% 3.93/0.93      inference(renaming,[status(thm)],[c_239]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_21,plain,
% 3.93/0.93      ( r1_yellow_0(X0,k1_xboole_0)
% 3.93/0.93      | v2_struct_0(X0)
% 3.93/0.93      | ~ v5_orders_2(X0)
% 3.93/0.93      | ~ v1_yellow_0(X0)
% 3.93/0.93      | ~ l1_orders_2(X0) ),
% 3.93/0.93      inference(cnf_transformation,[],[f90]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_36,negated_conjecture,
% 3.93/0.93      ( v1_yellow_0(sK6) ),
% 3.93/0.93      inference(cnf_transformation,[],[f101]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_525,plain,
% 3.93/0.93      ( r1_yellow_0(X0,k1_xboole_0)
% 3.93/0.93      | v2_struct_0(X0)
% 3.93/0.93      | ~ v5_orders_2(X0)
% 3.93/0.93      | ~ l1_orders_2(X0)
% 3.93/0.93      | sK6 != X0 ),
% 3.93/0.93      inference(resolution_lifted,[status(thm)],[c_21,c_36]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_526,plain,
% 3.93/0.93      ( r1_yellow_0(sK6,k1_xboole_0)
% 3.93/0.93      | v2_struct_0(sK6)
% 3.93/0.93      | ~ v5_orders_2(sK6)
% 3.93/0.93      | ~ l1_orders_2(sK6) ),
% 3.93/0.93      inference(unflattening,[status(thm)],[c_525]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_38,negated_conjecture,
% 3.93/0.93      ( ~ v2_struct_0(sK6) ),
% 3.93/0.93      inference(cnf_transformation,[],[f99]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_37,negated_conjecture,
% 3.93/0.93      ( v5_orders_2(sK6) ),
% 3.93/0.93      inference(cnf_transformation,[],[f100]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_71,plain,
% 3.93/0.93      ( r1_yellow_0(sK6,k1_xboole_0)
% 3.93/0.93      | v2_struct_0(sK6)
% 3.93/0.93      | ~ v5_orders_2(sK6)
% 3.93/0.93      | ~ v1_yellow_0(sK6)
% 3.93/0.93      | ~ l1_orders_2(sK6) ),
% 3.93/0.93      inference(instantiation,[status(thm)],[c_21]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_528,plain,
% 3.93/0.93      ( r1_yellow_0(sK6,k1_xboole_0) ),
% 3.93/0.93      inference(global_propositional_subsumption,
% 3.93/0.93                [status(thm)],
% 3.93/0.93                [c_526,c_38,c_37,c_36,c_35,c_71]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_628,plain,
% 3.93/0.93      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.93/0.93      | ~ r2_lattice3(X0,X1,X2)
% 3.93/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.93/0.93      | ~ l1_orders_2(X0)
% 3.93/0.93      | sK6 != X0
% 3.93/0.93      | k1_xboole_0 != X1 ),
% 3.93/0.93      inference(resolution_lifted,[status(thm)],[c_240,c_528]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_629,plain,
% 3.93/0.93      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
% 3.93/0.93      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 3.93/0.93      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.93/0.93      | ~ l1_orders_2(sK6) ),
% 3.93/0.93      inference(unflattening,[status(thm)],[c_628]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_633,plain,
% 3.93/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.93/0.93      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 3.93/0.93      | r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) ),
% 3.93/0.93      inference(global_propositional_subsumption,
% 3.93/0.93                [status(thm)],
% 3.93/0.93                [c_629,c_35]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_634,plain,
% 3.93/0.93      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
% 3.93/0.93      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 3.93/0.93      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 3.93/0.93      inference(renaming,[status(thm)],[c_633]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2562,plain,
% 3.93/0.93      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) = iProver_top
% 3.93/0.93      | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 3.93/0.93      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_14,plain,
% 3.93/0.93      ( ~ l1_orders_2(X0)
% 3.93/0.93      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 3.93/0.93      inference(cnf_transformation,[],[f83]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_802,plain,
% 3.93/0.93      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK6 != X0 ),
% 3.93/0.93      inference(resolution_lifted,[status(thm)],[c_14,c_35]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_803,plain,
% 3.93/0.93      ( k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
% 3.93/0.93      inference(unflattening,[status(thm)],[c_802]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2579,plain,
% 3.93/0.93      ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
% 3.93/0.93      | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 3.93/0.93      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.93/0.93      inference(light_normalisation,[status(thm)],[c_2562,c_803]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_4369,plain,
% 3.93/0.93      ( r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 3.93/0.93      | r2_hidden(X0,sK7) = iProver_top
% 3.93/0.93      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
% 3.93/0.93      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_2579,c_4364]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2577,plain,
% 3.93/0.93      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_1,plain,
% 3.93/0.93      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.93/0.93      inference(cnf_transformation,[],[f70]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2576,plain,
% 3.93/0.93      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2,plain,
% 3.93/0.93      ( r2_hidden(sK0(X0,X1),X1)
% 3.93/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 3.93/0.93      | k1_xboole_0 = X1 ),
% 3.93/0.93      inference(cnf_transformation,[],[f72]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2575,plain,
% 3.93/0.93      ( k1_xboole_0 = X0
% 3.93/0.93      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 3.93/0.93      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_9,plain,
% 3.93/0.93      ( ~ r2_hidden(X0,X1)
% 3.93/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.93/0.93      | ~ v1_xboole_0(X2) ),
% 3.93/0.93      inference(cnf_transformation,[],[f78]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2568,plain,
% 3.93/0.93      ( r2_hidden(X0,X1) != iProver_top
% 3.93/0.93      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.93/0.93      | v1_xboole_0(X2) != iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_3918,plain,
% 3.93/0.93      ( r2_hidden(X0,k2_subset_1(X1)) != iProver_top
% 3.93/0.93      | v1_xboole_0(X1) != iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_2576,c_2568]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_4728,plain,
% 3.93/0.93      ( k2_subset_1(X0) = k1_xboole_0
% 3.93/0.93      | m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X1)) != iProver_top
% 3.93/0.93      | v1_xboole_0(X0) != iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_2575,c_3918]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_5688,plain,
% 3.93/0.93      ( k2_subset_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_2576,c_4728]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_6028,plain,
% 3.93/0.93      ( k2_subset_1(k1_xboole_0) = k1_xboole_0 ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_2577,c_5688]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_4729,plain,
% 3.93/0.93      ( r2_lattice3(sK6,k2_subset_1(X0),X1) = iProver_top
% 3.93/0.93      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.93/0.93      | v1_xboole_0(X0) != iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_2552,c_3918]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_6157,plain,
% 3.93/0.93      ( r2_lattice3(sK6,k1_xboole_0,X0) = iProver_top
% 3.93/0.93      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.93/0.93      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_6028,c_4729]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_19,plain,
% 3.93/0.93      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 3.93/0.93      | ~ r1_yellow_0(X0,X1)
% 3.93/0.93      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.93/0.93      | ~ l1_orders_2(X0) ),
% 3.93/0.93      inference(cnf_transformation,[],[f109]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_232,plain,
% 3.93/0.93      ( ~ r1_yellow_0(X0,X1)
% 3.93/0.93      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 3.93/0.93      | ~ l1_orders_2(X0) ),
% 3.93/0.93      inference(global_propositional_subsumption,
% 3.93/0.93                [status(thm)],
% 3.93/0.93                [c_19,c_20]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_233,plain,
% 3.93/0.93      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 3.93/0.93      | ~ r1_yellow_0(X0,X1)
% 3.93/0.93      | ~ l1_orders_2(X0) ),
% 3.93/0.93      inference(renaming,[status(thm)],[c_232]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_649,plain,
% 3.93/0.93      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 3.93/0.93      | ~ l1_orders_2(X0)
% 3.93/0.93      | sK6 != X0
% 3.93/0.93      | k1_xboole_0 != X1 ),
% 3.93/0.93      inference(resolution_lifted,[status(thm)],[c_233,c_528]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_650,plain,
% 3.93/0.93      ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0))
% 3.93/0.93      | ~ l1_orders_2(sK6) ),
% 3.93/0.93      inference(unflattening,[status(thm)],[c_649]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_652,plain,
% 3.93/0.93      ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0)) ),
% 3.93/0.93      inference(global_propositional_subsumption,
% 3.93/0.93                [status(thm)],
% 3.93/0.93                [c_650,c_35]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2561,plain,
% 3.93/0.93      ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0)) = iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_652]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2578,plain,
% 3.93/0.93      ( r2_lattice3(sK6,k1_xboole_0,k3_yellow_0(sK6)) = iProver_top ),
% 3.93/0.93      inference(light_normalisation,[status(thm)],[c_2561,c_803]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_793,plain,
% 3.93/0.93      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK6 != X0 ),
% 3.93/0.93      inference(resolution_lifted,[status(thm)],[c_20,c_35]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_794,plain,
% 3.93/0.93      ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
% 3.93/0.93      inference(unflattening,[status(thm)],[c_793]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2555,plain,
% 3.93/0.93      ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_794]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2929,plain,
% 3.93/0.93      ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_803,c_2555]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2569,plain,
% 3.93/0.93      ( r2_hidden(X0,X1) != iProver_top
% 3.93/0.93      | m1_subset_1(X0,X2) = iProver_top
% 3.93/0.93      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_4238,plain,
% 3.93/0.93      ( r2_hidden(X0,sK7) != iProver_top
% 3.93/0.93      | m1_subset_1(X0,u1_struct_0(sK6)) = iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_2567,c_2569]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_4358,plain,
% 3.93/0.93      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 3.93/0.93      | r2_lattice3(sK6,X2,X1) != iProver_top
% 3.93/0.93      | r2_hidden(X0,X2) != iProver_top
% 3.93/0.93      | r2_hidden(X0,sK7) != iProver_top
% 3.93/0.93      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_4238,c_2554]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_4640,plain,
% 3.93/0.93      ( r1_orders_2(sK6,X0,k3_yellow_0(sK6)) = iProver_top
% 3.93/0.93      | r2_lattice3(sK6,X1,k3_yellow_0(sK6)) != iProver_top
% 3.93/0.93      | r2_hidden(X0,X1) != iProver_top
% 3.93/0.93      | r2_hidden(X0,sK7) != iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_2929,c_4358]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_4840,plain,
% 3.93/0.93      ( r1_orders_2(sK6,X0,k3_yellow_0(sK6)) = iProver_top
% 3.93/0.93      | r2_hidden(X0,sK7) != iProver_top
% 3.93/0.93      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_2578,c_4640]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_5114,plain,
% 3.93/0.93      ( r2_hidden(X0,sK7) != iProver_top
% 3.93/0.93      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.93/0.93      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
% 3.93/0.93      | m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_4840,c_4364]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_5123,plain,
% 3.93/0.93      ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
% 3.93/0.93      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.93/0.93      | r2_hidden(X0,sK7) != iProver_top ),
% 3.93/0.93      inference(global_propositional_subsumption,
% 3.93/0.93                [status(thm)],
% 3.93/0.93                [c_5114,c_2929]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_5124,plain,
% 3.93/0.93      ( r2_hidden(X0,sK7) != iProver_top
% 3.93/0.93      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.93/0.93      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.93/0.93      inference(renaming,[status(thm)],[c_5123]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_5129,plain,
% 3.93/0.93      ( sK7 = k1_xboole_0
% 3.93/0.93      | r2_hidden(sK0(X0,sK7),k1_xboole_0) != iProver_top
% 3.93/0.93      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
% 3.93/0.93      | m1_subset_1(sK7,k1_zfmisc_1(X0)) != iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_2575,c_5124]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_34,negated_conjecture,
% 3.93/0.93      ( ~ v1_xboole_0(sK7) ),
% 3.93/0.93      inference(cnf_transformation,[],[f103]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_43,plain,
% 3.93/0.93      ( v1_xboole_0(sK7) != iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_28,plain,
% 3.93/0.93      ( v1_subset_1(X0,X1)
% 3.93/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.93/0.93      | X0 = X1 ),
% 3.93/0.93      inference(cnf_transformation,[],[f98]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_30,negated_conjecture,
% 3.93/0.93      ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
% 3.93/0.93      | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.93/0.93      inference(cnf_transformation,[],[f107]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_310,plain,
% 3.93/0.93      ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
% 3.93/0.93      | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.93/0.93      inference(prop_impl,[status(thm)],[c_30]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_594,plain,
% 3.93/0.93      ( r2_hidden(k3_yellow_0(sK6),sK7)
% 3.93/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.93/0.93      | X1 = X0
% 3.93/0.93      | u1_struct_0(sK6) != X1
% 3.93/0.93      | sK7 != X0 ),
% 3.93/0.93      inference(resolution_lifted,[status(thm)],[c_28,c_310]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_595,plain,
% 3.93/0.93      ( r2_hidden(k3_yellow_0(sK6),sK7)
% 3.93/0.93      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.93/0.93      | u1_struct_0(sK6) = sK7 ),
% 3.93/0.93      inference(unflattening,[status(thm)],[c_594]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_596,plain,
% 3.93/0.93      ( u1_struct_0(sK6) = sK7
% 3.93/0.93      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
% 3.93/0.93      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_595]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2027,plain,
% 3.93/0.93      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 3.93/0.93      theory(equality) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2041,plain,
% 3.93/0.93      ( k3_yellow_0(sK6) = k3_yellow_0(sK6) | sK6 != sK6 ),
% 3.93/0.93      inference(instantiation,[status(thm)],[c_2027]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2017,plain,( X0 = X0 ),theory(equality) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2048,plain,
% 3.93/0.93      ( sK6 = sK6 ),
% 3.93/0.93      inference(instantiation,[status(thm)],[c_2017]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_4086,plain,
% 3.93/0.93      ( sK7 = sK7 ),
% 3.93/0.93      inference(instantiation,[status(thm)],[c_2017]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2018,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_3205,plain,
% 3.93/0.93      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 3.93/0.93      inference(instantiation,[status(thm)],[c_2018]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_4090,plain,
% 3.93/0.93      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 3.93/0.93      inference(instantiation,[status(thm)],[c_3205]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_5399,plain,
% 3.93/0.93      ( u1_struct_0(sK6) != sK7 | sK7 = u1_struct_0(sK6) | sK7 != sK7 ),
% 3.93/0.93      inference(instantiation,[status(thm)],[c_4090]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2021,plain,
% 3.93/0.93      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.93/0.93      theory(equality) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_3955,plain,
% 3.93/0.93      ( m1_subset_1(X0,X1)
% 3.93/0.93      | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
% 3.93/0.93      | X0 != k3_yellow_0(sK6)
% 3.93/0.93      | X1 != u1_struct_0(sK6) ),
% 3.93/0.93      inference(instantiation,[status(thm)],[c_2021]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_4818,plain,
% 3.93/0.93      ( m1_subset_1(k3_yellow_0(sK6),X0)
% 3.93/0.93      | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
% 3.93/0.93      | X0 != u1_struct_0(sK6)
% 3.93/0.93      | k3_yellow_0(sK6) != k3_yellow_0(sK6) ),
% 3.93/0.93      inference(instantiation,[status(thm)],[c_3955]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_5850,plain,
% 3.93/0.93      ( ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
% 3.93/0.93      | m1_subset_1(k3_yellow_0(sK6),sK7)
% 3.93/0.93      | k3_yellow_0(sK6) != k3_yellow_0(sK6)
% 3.93/0.93      | sK7 != u1_struct_0(sK6) ),
% 3.93/0.93      inference(instantiation,[status(thm)],[c_4818]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_5851,plain,
% 3.93/0.93      ( k3_yellow_0(sK6) != k3_yellow_0(sK6)
% 3.93/0.93      | sK7 != u1_struct_0(sK6)
% 3.93/0.93      | m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top
% 3.93/0.93      | m1_subset_1(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_5850]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_7,plain,
% 3.93/0.93      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 3.93/0.93      inference(cnf_transformation,[],[f76]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2647,plain,
% 3.93/0.93      ( r2_hidden(X0,sK7) | ~ m1_subset_1(X0,sK7) | v1_xboole_0(sK7) ),
% 3.93/0.93      inference(instantiation,[status(thm)],[c_7]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_6977,plain,
% 3.93/0.93      ( r2_hidden(k3_yellow_0(sK6),sK7)
% 3.93/0.93      | ~ m1_subset_1(k3_yellow_0(sK6),sK7)
% 3.93/0.93      | v1_xboole_0(sK7) ),
% 3.93/0.93      inference(instantiation,[status(thm)],[c_2647]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_6978,plain,
% 3.93/0.93      ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
% 3.93/0.93      | m1_subset_1(k3_yellow_0(sK6),sK7) != iProver_top
% 3.93/0.93      | v1_xboole_0(sK7) = iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_6977]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_7677,plain,
% 3.93/0.93      ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.93/0.93      inference(global_propositional_subsumption,
% 3.93/0.93                [status(thm)],
% 3.93/0.93                [c_5129,c_43,c_45,c_596,c_2041,c_2048,c_2929,c_4086,
% 3.93/0.93                 c_5399,c_5851,c_6978]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_8067,plain,
% 3.93/0.93      ( r2_hidden(X0,sK7) = iProver_top
% 3.93/0.93      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.93/0.93      inference(global_propositional_subsumption,
% 3.93/0.93                [status(thm)],
% 3.93/0.93                [c_8041,c_43,c_45,c_133,c_596,c_2041,c_2048,c_2929,
% 3.93/0.93                 c_4086,c_4369,c_5399,c_5851,c_6157,c_6978]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_8074,plain,
% 3.93/0.93      ( u1_struct_0(sK6) = X0
% 3.93/0.93      | r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top
% 3.93/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_2572,c_8067]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_4,plain,
% 3.93/0.93      ( ~ r2_hidden(sK1(X0,X1),X1)
% 3.93/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 3.93/0.93      | X1 = X0 ),
% 3.93/0.93      inference(cnf_transformation,[],[f74]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2573,plain,
% 3.93/0.93      ( X0 = X1
% 3.93/0.93      | r2_hidden(sK1(X1,X0),X0) != iProver_top
% 3.93/0.93      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.93/0.93      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_9493,plain,
% 3.93/0.93      ( u1_struct_0(sK6) = sK7
% 3.93/0.93      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.93/0.93      inference(superposition,[status(thm)],[c_8074,c_2573]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_7679,plain,
% 3.93/0.93      ( r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.93/0.93      inference(predicate_to_equality_rev,[status(thm)],[c_7677]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_2673,plain,
% 3.93/0.93      ( ~ m1_subset_1(X0,X1)
% 3.93/0.93      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.93/0.93      | X2 != X0
% 3.93/0.93      | k1_zfmisc_1(u1_struct_0(sK6)) != X1 ),
% 3.93/0.93      inference(instantiation,[status(thm)],[c_2021]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_3033,plain,
% 3.93/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.93/0.93      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.93/0.93      | X1 != X0
% 3.93/0.93      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
% 3.93/0.93      inference(instantiation,[status(thm)],[c_2673]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_4215,plain,
% 3.93/0.93      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.93/0.93      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.93/0.93      | X0 != sK7
% 3.93/0.93      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
% 3.93/0.93      inference(instantiation,[status(thm)],[c_3033]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_5019,plain,
% 3.93/0.93      ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.93/0.93      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.93/0.93      | u1_struct_0(sK6) != sK7
% 3.93/0.93      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
% 3.93/0.93      inference(instantiation,[status(thm)],[c_4215]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_3470,plain,
% 3.93/0.93      ( k1_zfmisc_1(u1_struct_0(sK6)) = k1_zfmisc_1(u1_struct_0(sK6)) ),
% 3.93/0.93      inference(instantiation,[status(thm)],[c_2017]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_29,plain,
% 3.93/0.93      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 3.93/0.93      inference(cnf_transformation,[],[f110]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_31,negated_conjecture,
% 3.93/0.93      ( v1_subset_1(sK7,u1_struct_0(sK6))
% 3.93/0.93      | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.93/0.93      inference(cnf_transformation,[],[f106]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_308,plain,
% 3.93/0.93      ( v1_subset_1(sK7,u1_struct_0(sK6))
% 3.93/0.93      | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.93/0.93      inference(prop_impl,[status(thm)],[c_31]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_608,plain,
% 3.93/0.93      ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 3.93/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 3.93/0.93      | u1_struct_0(sK6) != X0
% 3.93/0.93      | sK7 != X0 ),
% 3.93/0.93      inference(resolution_lifted,[status(thm)],[c_29,c_308]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(c_609,plain,
% 3.93/0.93      ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 3.93/0.93      | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.93/0.93      | sK7 != u1_struct_0(sK6) ),
% 3.93/0.93      inference(unflattening,[status(thm)],[c_608]) ).
% 3.93/0.93  
% 3.93/0.93  cnf(contradiction,plain,
% 3.93/0.93      ( $false ),
% 3.93/0.93      inference(minisat,
% 3.93/0.93                [status(thm)],
% 3.93/0.93                [c_9493,c_7679,c_5399,c_5019,c_4086,c_3470,c_609,c_45,
% 3.93/0.93                 c_32]) ).
% 3.93/0.93  
% 3.93/0.93  
% 3.93/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 3.93/0.93  
% 3.93/0.93  ------                               Statistics
% 3.93/0.93  
% 3.93/0.93  ------ General
% 3.93/0.93  
% 3.93/0.93  abstr_ref_over_cycles:                  0
% 3.93/0.93  abstr_ref_under_cycles:                 0
% 3.93/0.93  gc_basic_clause_elim:                   0
% 3.93/0.93  forced_gc_time:                         0
% 3.93/0.93  parsing_time:                           0.008
% 3.93/0.93  unif_index_cands_time:                  0.
% 3.93/0.93  unif_index_add_time:                    0.
% 3.93/0.93  orderings_time:                         0.
% 3.93/0.93  out_proof_time:                         0.013
% 3.93/0.93  total_time:                             0.281
% 3.93/0.93  num_of_symbols:                         57
% 3.93/0.93  num_of_terms:                           8758
% 3.93/0.93  
% 3.93/0.93  ------ Preprocessing
% 3.93/0.93  
% 3.93/0.93  num_of_splits:                          0
% 3.93/0.93  num_of_split_atoms:                     0
% 3.93/0.93  num_of_reused_defs:                     0
% 3.93/0.93  num_eq_ax_congr_red:                    40
% 3.93/0.93  num_of_sem_filtered_clauses:            1
% 3.93/0.93  num_of_subtypes:                        0
% 3.93/0.93  monotx_restored_types:                  0
% 3.93/0.93  sat_num_of_epr_types:                   0
% 3.93/0.93  sat_num_of_non_cyclic_types:            0
% 3.93/0.93  sat_guarded_non_collapsed_types:        0
% 3.93/0.93  num_pure_diseq_elim:                    0
% 3.93/0.93  simp_replaced_by:                       0
% 3.93/0.93  res_preprocessed:                       168
% 3.93/0.93  prep_upred:                             0
% 3.93/0.93  prep_unflattend:                        72
% 3.93/0.93  smt_new_axioms:                         0
% 3.93/0.93  pred_elim_cands:                        6
% 3.93/0.93  pred_elim:                              6
% 3.93/0.93  pred_elim_cl:                           7
% 3.93/0.93  pred_elim_cycles:                       12
% 3.93/0.93  merged_defs:                            2
% 3.93/0.93  merged_defs_ncl:                        0
% 3.93/0.93  bin_hyper_res:                          2
% 3.93/0.93  prep_cycles:                            4
% 3.93/0.93  pred_elim_time:                         0.015
% 3.93/0.93  splitting_time:                         0.
% 3.93/0.93  sem_filter_time:                        0.
% 3.93/0.93  monotx_time:                            0.
% 3.93/0.93  subtype_inf_time:                       0.
% 3.93/0.93  
% 3.93/0.93  ------ Problem properties
% 3.93/0.93  
% 3.93/0.93  clauses:                                32
% 3.93/0.93  conjectures:                            3
% 3.93/0.93  epr:                                    5
% 3.93/0.93  horn:                                   19
% 3.93/0.93  ground:                                 8
% 3.93/0.93  unary:                                  8
% 3.93/0.93  binary:                                 2
% 3.93/0.93  lits:                                   86
% 3.93/0.93  lits_eq:                                10
% 3.93/0.93  fd_pure:                                0
% 3.93/0.93  fd_pseudo:                              0
% 3.93/0.93  fd_cond:                                5
% 3.93/0.93  fd_pseudo_cond:                         2
% 3.93/0.93  ac_symbols:                             0
% 3.93/0.93  
% 3.93/0.93  ------ Propositional Solver
% 3.93/0.93  
% 3.93/0.93  prop_solver_calls:                      29
% 3.93/0.93  prop_fast_solver_calls:                 1807
% 3.93/0.93  smt_solver_calls:                       0
% 3.93/0.93  smt_fast_solver_calls:                  0
% 3.93/0.93  prop_num_of_clauses:                    3989
% 3.93/0.93  prop_preprocess_simplified:             9904
% 3.93/0.93  prop_fo_subsumed:                       54
% 3.93/0.93  prop_solver_time:                       0.
% 3.93/0.93  smt_solver_time:                        0.
% 3.93/0.93  smt_fast_solver_time:                   0.
% 3.93/0.93  prop_fast_solver_time:                  0.
% 3.93/0.93  prop_unsat_core_time:                   0.
% 3.93/0.93  
% 3.93/0.93  ------ QBF
% 3.93/0.93  
% 3.93/0.93  qbf_q_res:                              0
% 3.93/0.93  qbf_num_tautologies:                    0
% 3.93/0.93  qbf_prep_cycles:                        0
% 3.93/0.93  
% 3.93/0.93  ------ BMC1
% 3.93/0.93  
% 3.93/0.93  bmc1_current_bound:                     -1
% 3.93/0.93  bmc1_last_solved_bound:                 -1
% 3.93/0.93  bmc1_unsat_core_size:                   -1
% 3.93/0.93  bmc1_unsat_core_parents_size:           -1
% 3.93/0.93  bmc1_merge_next_fun:                    0
% 3.93/0.93  bmc1_unsat_core_clauses_time:           0.
% 3.93/0.93  
% 3.93/0.93  ------ Instantiation
% 3.93/0.93  
% 3.93/0.93  inst_num_of_clauses:                    999
% 3.93/0.93  inst_num_in_passive:                    159
% 3.93/0.93  inst_num_in_active:                     618
% 3.93/0.93  inst_num_in_unprocessed:                222
% 3.93/0.93  inst_num_of_loops:                      680
% 3.93/0.93  inst_num_of_learning_restarts:          0
% 3.93/0.93  inst_num_moves_active_passive:          59
% 3.93/0.93  inst_lit_activity:                      0
% 3.93/0.93  inst_lit_activity_moves:                0
% 3.93/0.93  inst_num_tautologies:                   0
% 3.93/0.93  inst_num_prop_implied:                  0
% 3.93/0.93  inst_num_existing_simplified:           0
% 3.93/0.93  inst_num_eq_res_simplified:             0
% 3.93/0.93  inst_num_child_elim:                    0
% 3.93/0.93  inst_num_of_dismatching_blockings:      368
% 3.93/0.93  inst_num_of_non_proper_insts:           1331
% 3.93/0.93  inst_num_of_duplicates:                 0
% 3.93/0.93  inst_inst_num_from_inst_to_res:         0
% 3.93/0.93  inst_dismatching_checking_time:         0.
% 3.93/0.93  
% 3.93/0.93  ------ Resolution
% 3.93/0.93  
% 3.93/0.93  res_num_of_clauses:                     0
% 3.93/0.93  res_num_in_passive:                     0
% 3.93/0.93  res_num_in_active:                      0
% 3.93/0.93  res_num_of_loops:                       172
% 3.93/0.93  res_forward_subset_subsumed:            143
% 3.93/0.93  res_backward_subset_subsumed:           0
% 3.93/0.93  res_forward_subsumed:                   0
% 3.93/0.93  res_backward_subsumed:                  0
% 3.93/0.93  res_forward_subsumption_resolution:     6
% 3.93/0.93  res_backward_subsumption_resolution:    0
% 3.93/0.93  res_clause_to_clause_subsumption:       881
% 3.93/0.93  res_orphan_elimination:                 0
% 3.93/0.93  res_tautology_del:                      90
% 3.93/0.93  res_num_eq_res_simplified:              0
% 3.93/0.93  res_num_sel_changes:                    0
% 3.93/0.93  res_moves_from_active_to_pass:          0
% 3.93/0.93  
% 3.93/0.93  ------ Superposition
% 3.93/0.93  
% 3.93/0.93  sup_time_total:                         0.
% 3.93/0.93  sup_time_generating:                    0.
% 3.93/0.93  sup_time_sim_full:                      0.
% 3.93/0.93  sup_time_sim_immed:                     0.
% 3.93/0.93  
% 3.93/0.93  sup_num_of_clauses:                     242
% 3.93/0.93  sup_num_in_active:                      118
% 3.93/0.93  sup_num_in_passive:                     124
% 3.93/0.93  sup_num_of_loops:                       134
% 3.93/0.93  sup_fw_superposition:                   161
% 3.93/0.93  sup_bw_superposition:                   171
% 3.93/0.93  sup_immediate_simplified:               73
% 3.93/0.93  sup_given_eliminated:                   0
% 3.93/0.93  comparisons_done:                       0
% 3.93/0.93  comparisons_avoided:                    0
% 3.93/0.93  
% 3.93/0.93  ------ Simplifications
% 3.93/0.93  
% 3.93/0.93  
% 3.93/0.93  sim_fw_subset_subsumed:                 35
% 3.93/0.93  sim_bw_subset_subsumed:                 2
% 3.93/0.93  sim_fw_subsumed:                        32
% 3.93/0.93  sim_bw_subsumed:                        21
% 3.93/0.93  sim_fw_subsumption_res:                 0
% 3.93/0.93  sim_bw_subsumption_res:                 0
% 3.93/0.93  sim_tautology_del:                      3
% 3.93/0.93  sim_eq_tautology_del:                   5
% 3.93/0.93  sim_eq_res_simp:                        0
% 3.93/0.93  sim_fw_demodulated:                     4
% 3.93/0.93  sim_bw_demodulated:                     0
% 3.93/0.93  sim_light_normalised:                   4
% 3.93/0.93  sim_joinable_taut:                      0
% 3.93/0.93  sim_joinable_simp:                      0
% 3.93/0.93  sim_ac_normalised:                      0
% 3.93/0.93  sim_smt_subsumption:                    0
% 3.93/0.93  
%------------------------------------------------------------------------------
