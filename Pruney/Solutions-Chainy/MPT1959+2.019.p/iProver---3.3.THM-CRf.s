%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:27 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  222 (2391 expanded)
%              Number of clauses        :  130 ( 544 expanded)
%              Number of leaves         :   25 ( 461 expanded)
%              Depth                    :   26
%              Number of atoms          :  952 (19636 expanded)
%              Number of equality atoms :  218 ( 696 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f42])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | m1_subset_1(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
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

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

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
    inference(nnf_transformation,[],[f37])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f62,plain,(
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

fof(f61,plain,
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

fof(f63,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f60,f62,f61])).

fof(f94,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f97,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f63])).

fof(f11,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f54,f56,f55])).

fof(f83,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f96,plain,(
    v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f95,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f63])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f75,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f82,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f93,plain,(
    v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f91,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f92,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f99,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | ~ v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f63])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f102,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f98,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK1(X1,X0),X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2503,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_819,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_32])).

cnf(c_820,plain,
    ( r2_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(sK2(sK6,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_819])).

cnf(c_2485,plain,
    ( r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_820])).

cnf(c_9,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_804,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_32])).

cnf(c_805,plain,
    ( r2_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_804])).

cnf(c_2486,plain,
    ( r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_805])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_783,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_32])).

cnf(c_784,plain,
    ( r1_orders_2(sK6,X0,X1)
    | ~ r2_lattice3(sK6,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X0,X2) ),
    inference(unflattening,[status(thm)],[c_783])).

cnf(c_2487,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r2_lattice3(sK6,X2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_784])).

cnf(c_3529,plain,
    ( r1_orders_2(sK6,sK2(sK6,X0,X1),X2) = iProver_top
    | r2_lattice3(sK6,X3,X2) != iProver_top
    | r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0,X1),X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2486,c_2487])).

cnf(c_6333,plain,
    ( r1_orders_2(sK6,sK2(sK6,X0,X1),X2) = iProver_top
    | r2_lattice3(sK6,X0,X2) != iProver_top
    | r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2485,c_3529])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2500,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_24,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_729,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_730,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(X2,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_729])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_746,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(X2,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_730,c_6])).

cnf(c_2490,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_3985,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2500,c_2490])).

cnf(c_30,negated_conjecture,
    ( v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_957,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK7 != X2
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_746])).

cnf(c_958,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7) ),
    inference(unflattening,[status(thm)],[c_957])).

cnf(c_960,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r1_orders_2(sK6,X0,X1)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_958,c_29])).

cnf(c_961,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7) ),
    inference(renaming,[status(thm)],[c_960])).

cnf(c_962,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_961])).

cnf(c_4129,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3985,c_962])).

cnf(c_6679,plain,
    ( r2_lattice3(sK6,X0,X1) != iProver_top
    | r2_lattice3(sK6,X0,X2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top
    | r2_hidden(sK2(sK6,X0,X2),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_6333,c_4129])).

cnf(c_6686,plain,
    ( r2_lattice3(sK6,sK7,X0) != iProver_top
    | r2_lattice3(sK6,sK7,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2485,c_6679])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_40,plain,
    ( v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1997,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_2011,plain,
    ( k3_yellow_0(sK6) = k3_yellow_0(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1997])).

cnf(c_1987,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2018,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1987])).

cnf(c_11,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_778,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_32])).

cnf(c_779,plain,
    ( k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
    inference(unflattening,[status(thm)],[c_778])).

cnf(c_17,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_769,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_32])).

cnf(c_770,plain,
    ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_769])).

cnf(c_2488,plain,
    ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_770])).

cnf(c_2756,plain,
    ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_779,c_2488])).

cnf(c_3019,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1987])).

cnf(c_1992,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2685,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,sK7)
    | X2 != X0
    | sK7 != X1 ),
    inference(instantiation,[status(thm)],[c_1992])).

cnf(c_2888,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(X1,sK7)
    | X1 != X0
    | sK7 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2685])).

cnf(c_3052,plain,
    ( m1_subset_1(X0,sK7)
    | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
    | X0 != k3_yellow_0(sK6)
    | sK7 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2888])).

cnf(c_3834,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
    | m1_subset_1(k3_yellow_0(sK6),sK7)
    | k3_yellow_0(sK6) != k3_yellow_0(sK6)
    | sK7 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3052])).

cnf(c_3835,plain,
    ( k3_yellow_0(sK6) != k3_yellow_0(sK6)
    | sK7 != u1_struct_0(sK6)
    | m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3834])).

cnf(c_15,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_221,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_17])).

cnf(c_222,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_221])).

cnf(c_18,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_33,negated_conjecture,
    ( v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_488,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_33])).

cnf(c_489,plain,
    ( r1_yellow_0(sK6,k1_xboole_0)
    | v2_struct_0(sK6)
    | ~ v5_orders_2(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_34,negated_conjecture,
    ( v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_68,plain,
    ( r1_yellow_0(sK6,k1_xboole_0)
    | v2_struct_0(sK6)
    | ~ v5_orders_2(sK6)
    | ~ v1_yellow_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_491,plain,
    ( r1_yellow_0(sK6,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_35,c_34,c_33,c_32,c_68])).

cnf(c_628,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK6 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_222,c_491])).

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
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_32])).

cnf(c_634,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
    | ~ r2_lattice3(sK6,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_633])).

cnf(c_2494,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) = iProver_top
    | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_2509,plain,
    ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
    | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2494,c_779])).

cnf(c_4134,plain,
    ( r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2509,c_4129])).

cnf(c_16,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_214,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_17])).

cnf(c_215,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_214])).

cnf(c_649,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0)
    | sK6 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_215,c_491])).

cnf(c_650,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_649])).

cnf(c_652,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_650,c_32])).

cnf(c_2493,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_652])).

cnf(c_2508,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k3_yellow_0(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2493,c_779])).

cnf(c_2501,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3599,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2500,c_2501])).

cnf(c_3699,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r2_lattice3(sK6,X2,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3599,c_2487])).

cnf(c_4482,plain,
    ( r1_orders_2(sK6,X0,k3_yellow_0(sK6)) = iProver_top
    | r2_lattice3(sK6,X1,k3_yellow_0(sK6)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2756,c_3699])).

cnf(c_4693,plain,
    ( r1_orders_2(sK6,X0,k3_yellow_0(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_4482])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_532,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_533,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_534,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_533])).

cnf(c_4697,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4693,c_534])).

cnf(c_4702,plain,
    ( r2_lattice3(sK6,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2485,c_4697])).

cnf(c_25,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_27,negated_conjecture,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_287,plain,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(prop_impl,[status(thm)],[c_27])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK6),sK7)
    | X1 = X0
    | u1_struct_0(sK6) != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_287])).

cnf(c_571,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_573,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_29])).

cnf(c_2497,plain,
    ( u1_struct_0(sK6) = sK7
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_573])).

cnf(c_5037,plain,
    ( u1_struct_0(sK6) = sK7
    | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2497,c_4134])).

cnf(c_1988,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2668,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_1988])).

cnf(c_2735,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2668])).

cnf(c_5119,plain,
    ( u1_struct_0(sK6) != sK7
    | sK7 = u1_struct_0(sK6)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2735])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2572,plain,
    ( ~ m1_subset_1(X0,sK7)
    | r2_hidden(X0,sK7)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5797,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK6),sK7)
    | r2_hidden(k3_yellow_0(sK6),sK7)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_2572])).

cnf(c_5798,plain,
    ( m1_subset_1(k3_yellow_0(sK6),sK7) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5797])).

cnf(c_6756,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6686,c_40,c_2011,c_2018,c_2756,c_3019,c_3835,c_4134,c_4702,c_5037,c_5119,c_5798])).

cnf(c_6762,plain,
    ( u1_struct_0(sK6) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2503,c_6756])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X1,X0),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2504,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK1(X1,X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7076,plain,
    ( u1_struct_0(sK6) = sK7
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6762,c_2504])).

cnf(c_6769,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2756,c_6756])).

cnf(c_2585,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | X2 != X0
    | k1_zfmisc_1(u1_struct_0(sK6)) != X1 ),
    inference(instantiation,[status(thm)],[c_1992])).

cnf(c_2799,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | X1 != X0
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2585])).

cnf(c_4005,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | X0 != sK7
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2799])).

cnf(c_5118,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | u1_struct_0(sK6) != sK7
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_4005])).

cnf(c_5126,plain,
    ( u1_struct_0(sK6) != sK7
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5118])).

cnf(c_3222,plain,
    ( k1_zfmisc_1(u1_struct_0(sK6)) = k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_1987])).

cnf(c_26,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_28,negated_conjecture,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_285,plain,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(prop_impl,[status(thm)],[c_28])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) != X0
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_285])).

cnf(c_585,plain,
    ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | sK7 != u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_586,plain,
    ( sK7 != u1_struct_0(sK6)
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_585])).

cnf(c_42,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7076,c_6769,c_5126,c_5119,c_3222,c_3019,c_586,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.61/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.01  
% 3.61/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.61/1.01  
% 3.61/1.01  ------  iProver source info
% 3.61/1.01  
% 3.61/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.61/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.61/1.01  git: non_committed_changes: false
% 3.61/1.01  git: last_make_outside_of_git: false
% 3.61/1.01  
% 3.61/1.01  ------ 
% 3.61/1.01  
% 3.61/1.01  ------ Input Options
% 3.61/1.01  
% 3.61/1.01  --out_options                           all
% 3.61/1.01  --tptp_safe_out                         true
% 3.61/1.01  --problem_path                          ""
% 3.61/1.01  --include_path                          ""
% 3.61/1.01  --clausifier                            res/vclausify_rel
% 3.61/1.01  --clausifier_options                    ""
% 3.61/1.01  --stdin                                 false
% 3.61/1.01  --stats_out                             all
% 3.61/1.01  
% 3.61/1.01  ------ General Options
% 3.61/1.01  
% 3.61/1.01  --fof                                   false
% 3.61/1.01  --time_out_real                         305.
% 3.61/1.01  --time_out_virtual                      -1.
% 3.61/1.01  --symbol_type_check                     false
% 3.61/1.01  --clausify_out                          false
% 3.61/1.01  --sig_cnt_out                           false
% 3.61/1.01  --trig_cnt_out                          false
% 3.61/1.01  --trig_cnt_out_tolerance                1.
% 3.61/1.01  --trig_cnt_out_sk_spl                   false
% 3.61/1.01  --abstr_cl_out                          false
% 3.61/1.01  
% 3.61/1.01  ------ Global Options
% 3.61/1.01  
% 3.61/1.01  --schedule                              default
% 3.61/1.01  --add_important_lit                     false
% 3.61/1.01  --prop_solver_per_cl                    1000
% 3.61/1.01  --min_unsat_core                        false
% 3.61/1.01  --soft_assumptions                      false
% 3.61/1.01  --soft_lemma_size                       3
% 3.61/1.01  --prop_impl_unit_size                   0
% 3.61/1.01  --prop_impl_unit                        []
% 3.61/1.01  --share_sel_clauses                     true
% 3.61/1.01  --reset_solvers                         false
% 3.61/1.01  --bc_imp_inh                            [conj_cone]
% 3.61/1.01  --conj_cone_tolerance                   3.
% 3.61/1.01  --extra_neg_conj                        none
% 3.61/1.01  --large_theory_mode                     true
% 3.61/1.01  --prolific_symb_bound                   200
% 3.61/1.01  --lt_threshold                          2000
% 3.61/1.01  --clause_weak_htbl                      true
% 3.61/1.01  --gc_record_bc_elim                     false
% 3.61/1.01  
% 3.61/1.01  ------ Preprocessing Options
% 3.61/1.01  
% 3.61/1.01  --preprocessing_flag                    true
% 3.61/1.01  --time_out_prep_mult                    0.1
% 3.61/1.01  --splitting_mode                        input
% 3.61/1.01  --splitting_grd                         true
% 3.61/1.01  --splitting_cvd                         false
% 3.61/1.01  --splitting_cvd_svl                     false
% 3.61/1.01  --splitting_nvd                         32
% 3.61/1.01  --sub_typing                            true
% 3.61/1.01  --prep_gs_sim                           true
% 3.61/1.01  --prep_unflatten                        true
% 3.61/1.01  --prep_res_sim                          true
% 3.61/1.01  --prep_upred                            true
% 3.61/1.01  --prep_sem_filter                       exhaustive
% 3.61/1.01  --prep_sem_filter_out                   false
% 3.61/1.01  --pred_elim                             true
% 3.61/1.01  --res_sim_input                         true
% 3.61/1.01  --eq_ax_congr_red                       true
% 3.61/1.01  --pure_diseq_elim                       true
% 3.61/1.01  --brand_transform                       false
% 3.61/1.01  --non_eq_to_eq                          false
% 3.61/1.01  --prep_def_merge                        true
% 3.61/1.01  --prep_def_merge_prop_impl              false
% 3.61/1.01  --prep_def_merge_mbd                    true
% 3.61/1.01  --prep_def_merge_tr_red                 false
% 3.61/1.01  --prep_def_merge_tr_cl                  false
% 3.61/1.01  --smt_preprocessing                     true
% 3.61/1.01  --smt_ac_axioms                         fast
% 3.61/1.01  --preprocessed_out                      false
% 3.61/1.01  --preprocessed_stats                    false
% 3.61/1.01  
% 3.61/1.01  ------ Abstraction refinement Options
% 3.61/1.01  
% 3.61/1.01  --abstr_ref                             []
% 3.61/1.01  --abstr_ref_prep                        false
% 3.61/1.01  --abstr_ref_until_sat                   false
% 3.61/1.01  --abstr_ref_sig_restrict                funpre
% 3.61/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.61/1.01  --abstr_ref_under                       []
% 3.61/1.01  
% 3.61/1.01  ------ SAT Options
% 3.61/1.01  
% 3.61/1.01  --sat_mode                              false
% 3.61/1.01  --sat_fm_restart_options                ""
% 3.61/1.01  --sat_gr_def                            false
% 3.61/1.01  --sat_epr_types                         true
% 3.61/1.01  --sat_non_cyclic_types                  false
% 3.61/1.01  --sat_finite_models                     false
% 3.61/1.01  --sat_fm_lemmas                         false
% 3.61/1.01  --sat_fm_prep                           false
% 3.61/1.01  --sat_fm_uc_incr                        true
% 3.61/1.01  --sat_out_model                         small
% 3.61/1.01  --sat_out_clauses                       false
% 3.61/1.01  
% 3.61/1.01  ------ QBF Options
% 3.61/1.01  
% 3.61/1.01  --qbf_mode                              false
% 3.61/1.01  --qbf_elim_univ                         false
% 3.61/1.01  --qbf_dom_inst                          none
% 3.61/1.01  --qbf_dom_pre_inst                      false
% 3.61/1.01  --qbf_sk_in                             false
% 3.61/1.01  --qbf_pred_elim                         true
% 3.61/1.01  --qbf_split                             512
% 3.61/1.01  
% 3.61/1.01  ------ BMC1 Options
% 3.61/1.01  
% 3.61/1.01  --bmc1_incremental                      false
% 3.61/1.01  --bmc1_axioms                           reachable_all
% 3.61/1.01  --bmc1_min_bound                        0
% 3.61/1.01  --bmc1_max_bound                        -1
% 3.61/1.01  --bmc1_max_bound_default                -1
% 3.61/1.01  --bmc1_symbol_reachability              true
% 3.61/1.01  --bmc1_property_lemmas                  false
% 3.61/1.01  --bmc1_k_induction                      false
% 3.61/1.01  --bmc1_non_equiv_states                 false
% 3.61/1.01  --bmc1_deadlock                         false
% 3.61/1.01  --bmc1_ucm                              false
% 3.61/1.01  --bmc1_add_unsat_core                   none
% 3.61/1.01  --bmc1_unsat_core_children              false
% 3.61/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.61/1.01  --bmc1_out_stat                         full
% 3.61/1.01  --bmc1_ground_init                      false
% 3.61/1.01  --bmc1_pre_inst_next_state              false
% 3.61/1.01  --bmc1_pre_inst_state                   false
% 3.61/1.01  --bmc1_pre_inst_reach_state             false
% 3.61/1.01  --bmc1_out_unsat_core                   false
% 3.61/1.01  --bmc1_aig_witness_out                  false
% 3.61/1.01  --bmc1_verbose                          false
% 3.61/1.01  --bmc1_dump_clauses_tptp                false
% 3.61/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.61/1.01  --bmc1_dump_file                        -
% 3.61/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.61/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.61/1.01  --bmc1_ucm_extend_mode                  1
% 3.61/1.01  --bmc1_ucm_init_mode                    2
% 3.61/1.01  --bmc1_ucm_cone_mode                    none
% 3.61/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.61/1.01  --bmc1_ucm_relax_model                  4
% 3.61/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.61/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.61/1.01  --bmc1_ucm_layered_model                none
% 3.61/1.01  --bmc1_ucm_max_lemma_size               10
% 3.61/1.01  
% 3.61/1.01  ------ AIG Options
% 3.61/1.01  
% 3.61/1.01  --aig_mode                              false
% 3.61/1.01  
% 3.61/1.01  ------ Instantiation Options
% 3.61/1.01  
% 3.61/1.01  --instantiation_flag                    true
% 3.61/1.01  --inst_sos_flag                         true
% 3.61/1.01  --inst_sos_phase                        true
% 3.61/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.61/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.61/1.01  --inst_lit_sel_side                     num_symb
% 3.61/1.01  --inst_solver_per_active                1400
% 3.61/1.01  --inst_solver_calls_frac                1.
% 3.61/1.01  --inst_passive_queue_type               priority_queues
% 3.61/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.61/1.01  --inst_passive_queues_freq              [25;2]
% 3.61/1.01  --inst_dismatching                      true
% 3.61/1.01  --inst_eager_unprocessed_to_passive     true
% 3.61/1.01  --inst_prop_sim_given                   true
% 3.61/1.01  --inst_prop_sim_new                     false
% 3.61/1.01  --inst_subs_new                         false
% 3.61/1.01  --inst_eq_res_simp                      false
% 3.61/1.01  --inst_subs_given                       false
% 3.61/1.01  --inst_orphan_elimination               true
% 3.61/1.01  --inst_learning_loop_flag               true
% 3.61/1.01  --inst_learning_start                   3000
% 3.61/1.01  --inst_learning_factor                  2
% 3.61/1.01  --inst_start_prop_sim_after_learn       3
% 3.61/1.01  --inst_sel_renew                        solver
% 3.61/1.01  --inst_lit_activity_flag                true
% 3.61/1.01  --inst_restr_to_given                   false
% 3.61/1.01  --inst_activity_threshold               500
% 3.61/1.01  --inst_out_proof                        true
% 3.61/1.01  
% 3.61/1.01  ------ Resolution Options
% 3.61/1.01  
% 3.61/1.01  --resolution_flag                       true
% 3.61/1.01  --res_lit_sel                           adaptive
% 3.61/1.01  --res_lit_sel_side                      none
% 3.61/1.01  --res_ordering                          kbo
% 3.61/1.01  --res_to_prop_solver                    active
% 3.61/1.01  --res_prop_simpl_new                    false
% 3.61/1.01  --res_prop_simpl_given                  true
% 3.61/1.01  --res_passive_queue_type                priority_queues
% 3.61/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.61/1.01  --res_passive_queues_freq               [15;5]
% 3.61/1.01  --res_forward_subs                      full
% 3.61/1.01  --res_backward_subs                     full
% 3.61/1.01  --res_forward_subs_resolution           true
% 3.61/1.01  --res_backward_subs_resolution          true
% 3.61/1.01  --res_orphan_elimination                true
% 3.61/1.01  --res_time_limit                        2.
% 3.61/1.01  --res_out_proof                         true
% 3.61/1.01  
% 3.61/1.01  ------ Superposition Options
% 3.61/1.01  
% 3.61/1.01  --superposition_flag                    true
% 3.61/1.01  --sup_passive_queue_type                priority_queues
% 3.61/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.61/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.61/1.01  --demod_completeness_check              fast
% 3.61/1.01  --demod_use_ground                      true
% 3.61/1.01  --sup_to_prop_solver                    passive
% 3.61/1.01  --sup_prop_simpl_new                    true
% 3.61/1.01  --sup_prop_simpl_given                  true
% 3.61/1.01  --sup_fun_splitting                     true
% 3.61/1.01  --sup_smt_interval                      50000
% 3.61/1.01  
% 3.61/1.01  ------ Superposition Simplification Setup
% 3.61/1.01  
% 3.61/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.61/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.61/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.61/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.61/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.61/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.61/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.61/1.01  --sup_immed_triv                        [TrivRules]
% 3.61/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/1.01  --sup_immed_bw_main                     []
% 3.61/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.61/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.61/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/1.01  --sup_input_bw                          []
% 3.61/1.01  
% 3.61/1.01  ------ Combination Options
% 3.61/1.01  
% 3.61/1.01  --comb_res_mult                         3
% 3.61/1.01  --comb_sup_mult                         2
% 3.61/1.01  --comb_inst_mult                        10
% 3.61/1.01  
% 3.61/1.01  ------ Debug Options
% 3.61/1.01  
% 3.61/1.01  --dbg_backtrace                         false
% 3.61/1.01  --dbg_dump_prop_clauses                 false
% 3.61/1.01  --dbg_dump_prop_clauses_file            -
% 3.61/1.01  --dbg_out_stat                          false
% 3.61/1.01  ------ Parsing...
% 3.61/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.61/1.01  
% 3.61/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.61/1.01  
% 3.61/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.61/1.01  
% 3.61/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/1.01  ------ Proving...
% 3.61/1.01  ------ Problem Properties 
% 3.61/1.01  
% 3.61/1.01  
% 3.61/1.01  clauses                                 29
% 3.61/1.01  conjectures                             3
% 3.61/1.01  EPR                                     5
% 3.61/1.01  Horn                                    17
% 3.61/1.01  unary                                   7
% 3.61/1.01  binary                                  3
% 3.61/1.01  lits                                    78
% 3.61/1.01  lits eq                                 8
% 3.61/1.01  fd_pure                                 0
% 3.61/1.01  fd_pseudo                               0
% 3.61/1.01  fd_cond                                 3
% 3.61/1.01  fd_pseudo_cond                          2
% 3.61/1.01  AC symbols                              0
% 3.61/1.01  
% 3.61/1.01  ------ Schedule dynamic 5 is on 
% 3.61/1.01  
% 3.61/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.61/1.01  
% 3.61/1.01  
% 3.61/1.01  ------ 
% 3.61/1.01  Current options:
% 3.61/1.01  ------ 
% 3.61/1.01  
% 3.61/1.01  ------ Input Options
% 3.61/1.01  
% 3.61/1.01  --out_options                           all
% 3.61/1.01  --tptp_safe_out                         true
% 3.61/1.01  --problem_path                          ""
% 3.61/1.01  --include_path                          ""
% 3.61/1.01  --clausifier                            res/vclausify_rel
% 3.61/1.01  --clausifier_options                    ""
% 3.61/1.01  --stdin                                 false
% 3.61/1.01  --stats_out                             all
% 3.61/1.01  
% 3.61/1.01  ------ General Options
% 3.61/1.01  
% 3.61/1.01  --fof                                   false
% 3.61/1.01  --time_out_real                         305.
% 3.61/1.01  --time_out_virtual                      -1.
% 3.61/1.01  --symbol_type_check                     false
% 3.61/1.01  --clausify_out                          false
% 3.61/1.01  --sig_cnt_out                           false
% 3.61/1.01  --trig_cnt_out                          false
% 3.61/1.01  --trig_cnt_out_tolerance                1.
% 3.61/1.01  --trig_cnt_out_sk_spl                   false
% 3.61/1.01  --abstr_cl_out                          false
% 3.61/1.01  
% 3.61/1.01  ------ Global Options
% 3.61/1.01  
% 3.61/1.01  --schedule                              default
% 3.61/1.01  --add_important_lit                     false
% 3.61/1.01  --prop_solver_per_cl                    1000
% 3.61/1.01  --min_unsat_core                        false
% 3.61/1.01  --soft_assumptions                      false
% 3.61/1.01  --soft_lemma_size                       3
% 3.61/1.01  --prop_impl_unit_size                   0
% 3.61/1.01  --prop_impl_unit                        []
% 3.61/1.01  --share_sel_clauses                     true
% 3.61/1.01  --reset_solvers                         false
% 3.61/1.01  --bc_imp_inh                            [conj_cone]
% 3.61/1.01  --conj_cone_tolerance                   3.
% 3.61/1.01  --extra_neg_conj                        none
% 3.61/1.01  --large_theory_mode                     true
% 3.61/1.01  --prolific_symb_bound                   200
% 3.61/1.01  --lt_threshold                          2000
% 3.61/1.01  --clause_weak_htbl                      true
% 3.61/1.01  --gc_record_bc_elim                     false
% 3.61/1.01  
% 3.61/1.01  ------ Preprocessing Options
% 3.61/1.01  
% 3.61/1.01  --preprocessing_flag                    true
% 3.61/1.01  --time_out_prep_mult                    0.1
% 3.61/1.01  --splitting_mode                        input
% 3.61/1.01  --splitting_grd                         true
% 3.61/1.01  --splitting_cvd                         false
% 3.61/1.01  --splitting_cvd_svl                     false
% 3.61/1.01  --splitting_nvd                         32
% 3.61/1.01  --sub_typing                            true
% 3.61/1.01  --prep_gs_sim                           true
% 3.61/1.01  --prep_unflatten                        true
% 3.61/1.01  --prep_res_sim                          true
% 3.61/1.01  --prep_upred                            true
% 3.61/1.01  --prep_sem_filter                       exhaustive
% 3.61/1.01  --prep_sem_filter_out                   false
% 3.61/1.01  --pred_elim                             true
% 3.61/1.01  --res_sim_input                         true
% 3.61/1.01  --eq_ax_congr_red                       true
% 3.61/1.01  --pure_diseq_elim                       true
% 3.61/1.01  --brand_transform                       false
% 3.61/1.01  --non_eq_to_eq                          false
% 3.61/1.01  --prep_def_merge                        true
% 3.61/1.01  --prep_def_merge_prop_impl              false
% 3.61/1.01  --prep_def_merge_mbd                    true
% 3.61/1.01  --prep_def_merge_tr_red                 false
% 3.61/1.01  --prep_def_merge_tr_cl                  false
% 3.61/1.01  --smt_preprocessing                     true
% 3.61/1.01  --smt_ac_axioms                         fast
% 3.61/1.01  --preprocessed_out                      false
% 3.61/1.01  --preprocessed_stats                    false
% 3.61/1.01  
% 3.61/1.01  ------ Abstraction refinement Options
% 3.61/1.01  
% 3.61/1.01  --abstr_ref                             []
% 3.61/1.01  --abstr_ref_prep                        false
% 3.61/1.01  --abstr_ref_until_sat                   false
% 3.61/1.01  --abstr_ref_sig_restrict                funpre
% 3.61/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.61/1.01  --abstr_ref_under                       []
% 3.61/1.01  
% 3.61/1.01  ------ SAT Options
% 3.61/1.01  
% 3.61/1.01  --sat_mode                              false
% 3.61/1.01  --sat_fm_restart_options                ""
% 3.61/1.01  --sat_gr_def                            false
% 3.61/1.01  --sat_epr_types                         true
% 3.61/1.01  --sat_non_cyclic_types                  false
% 3.61/1.01  --sat_finite_models                     false
% 3.61/1.01  --sat_fm_lemmas                         false
% 3.61/1.01  --sat_fm_prep                           false
% 3.61/1.01  --sat_fm_uc_incr                        true
% 3.61/1.01  --sat_out_model                         small
% 3.61/1.01  --sat_out_clauses                       false
% 3.61/1.01  
% 3.61/1.01  ------ QBF Options
% 3.61/1.01  
% 3.61/1.01  --qbf_mode                              false
% 3.61/1.01  --qbf_elim_univ                         false
% 3.61/1.01  --qbf_dom_inst                          none
% 3.61/1.01  --qbf_dom_pre_inst                      false
% 3.61/1.01  --qbf_sk_in                             false
% 3.61/1.01  --qbf_pred_elim                         true
% 3.61/1.01  --qbf_split                             512
% 3.61/1.01  
% 3.61/1.01  ------ BMC1 Options
% 3.61/1.01  
% 3.61/1.01  --bmc1_incremental                      false
% 3.61/1.01  --bmc1_axioms                           reachable_all
% 3.61/1.01  --bmc1_min_bound                        0
% 3.61/1.01  --bmc1_max_bound                        -1
% 3.61/1.01  --bmc1_max_bound_default                -1
% 3.61/1.01  --bmc1_symbol_reachability              true
% 3.61/1.01  --bmc1_property_lemmas                  false
% 3.61/1.01  --bmc1_k_induction                      false
% 3.61/1.01  --bmc1_non_equiv_states                 false
% 3.61/1.01  --bmc1_deadlock                         false
% 3.61/1.01  --bmc1_ucm                              false
% 3.61/1.01  --bmc1_add_unsat_core                   none
% 3.61/1.01  --bmc1_unsat_core_children              false
% 3.61/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.61/1.01  --bmc1_out_stat                         full
% 3.61/1.01  --bmc1_ground_init                      false
% 3.61/1.01  --bmc1_pre_inst_next_state              false
% 3.61/1.01  --bmc1_pre_inst_state                   false
% 3.61/1.01  --bmc1_pre_inst_reach_state             false
% 3.61/1.01  --bmc1_out_unsat_core                   false
% 3.61/1.01  --bmc1_aig_witness_out                  false
% 3.61/1.01  --bmc1_verbose                          false
% 3.61/1.01  --bmc1_dump_clauses_tptp                false
% 3.61/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.61/1.01  --bmc1_dump_file                        -
% 3.61/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.61/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.61/1.01  --bmc1_ucm_extend_mode                  1
% 3.61/1.01  --bmc1_ucm_init_mode                    2
% 3.61/1.01  --bmc1_ucm_cone_mode                    none
% 3.61/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.61/1.01  --bmc1_ucm_relax_model                  4
% 3.61/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.61/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.61/1.01  --bmc1_ucm_layered_model                none
% 3.61/1.01  --bmc1_ucm_max_lemma_size               10
% 3.61/1.01  
% 3.61/1.01  ------ AIG Options
% 3.61/1.01  
% 3.61/1.01  --aig_mode                              false
% 3.61/1.01  
% 3.61/1.01  ------ Instantiation Options
% 3.61/1.01  
% 3.61/1.01  --instantiation_flag                    true
% 3.61/1.01  --inst_sos_flag                         true
% 3.61/1.01  --inst_sos_phase                        true
% 3.61/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.61/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.61/1.01  --inst_lit_sel_side                     none
% 3.61/1.01  --inst_solver_per_active                1400
% 3.61/1.01  --inst_solver_calls_frac                1.
% 3.61/1.01  --inst_passive_queue_type               priority_queues
% 3.61/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.61/1.01  --inst_passive_queues_freq              [25;2]
% 3.61/1.01  --inst_dismatching                      true
% 3.61/1.01  --inst_eager_unprocessed_to_passive     true
% 3.61/1.01  --inst_prop_sim_given                   true
% 3.61/1.01  --inst_prop_sim_new                     false
% 3.61/1.01  --inst_subs_new                         false
% 3.61/1.01  --inst_eq_res_simp                      false
% 3.61/1.01  --inst_subs_given                       false
% 3.61/1.01  --inst_orphan_elimination               true
% 3.61/1.01  --inst_learning_loop_flag               true
% 3.61/1.01  --inst_learning_start                   3000
% 3.61/1.01  --inst_learning_factor                  2
% 3.61/1.01  --inst_start_prop_sim_after_learn       3
% 3.61/1.01  --inst_sel_renew                        solver
% 3.61/1.01  --inst_lit_activity_flag                true
% 3.61/1.01  --inst_restr_to_given                   false
% 3.61/1.01  --inst_activity_threshold               500
% 3.61/1.01  --inst_out_proof                        true
% 3.61/1.01  
% 3.61/1.01  ------ Resolution Options
% 3.61/1.01  
% 3.61/1.01  --resolution_flag                       false
% 3.61/1.01  --res_lit_sel                           adaptive
% 3.61/1.01  --res_lit_sel_side                      none
% 3.61/1.01  --res_ordering                          kbo
% 3.61/1.01  --res_to_prop_solver                    active
% 3.61/1.01  --res_prop_simpl_new                    false
% 3.61/1.01  --res_prop_simpl_given                  true
% 3.61/1.01  --res_passive_queue_type                priority_queues
% 3.61/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.61/1.01  --res_passive_queues_freq               [15;5]
% 3.61/1.01  --res_forward_subs                      full
% 3.61/1.01  --res_backward_subs                     full
% 3.61/1.01  --res_forward_subs_resolution           true
% 3.61/1.01  --res_backward_subs_resolution          true
% 3.61/1.01  --res_orphan_elimination                true
% 3.61/1.01  --res_time_limit                        2.
% 3.61/1.01  --res_out_proof                         true
% 3.61/1.01  
% 3.61/1.01  ------ Superposition Options
% 3.61/1.01  
% 3.61/1.01  --superposition_flag                    true
% 3.61/1.01  --sup_passive_queue_type                priority_queues
% 3.61/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.61/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.61/1.01  --demod_completeness_check              fast
% 3.61/1.01  --demod_use_ground                      true
% 3.61/1.01  --sup_to_prop_solver                    passive
% 3.61/1.01  --sup_prop_simpl_new                    true
% 3.61/1.01  --sup_prop_simpl_given                  true
% 3.61/1.01  --sup_fun_splitting                     true
% 3.61/1.01  --sup_smt_interval                      50000
% 3.61/1.01  
% 3.61/1.01  ------ Superposition Simplification Setup
% 3.61/1.01  
% 3.61/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.61/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.61/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.61/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.61/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.61/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.61/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.61/1.01  --sup_immed_triv                        [TrivRules]
% 3.61/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/1.01  --sup_immed_bw_main                     []
% 3.61/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.61/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.61/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/1.01  --sup_input_bw                          []
% 3.61/1.01  
% 3.61/1.01  ------ Combination Options
% 3.61/1.01  
% 3.61/1.01  --comb_res_mult                         3
% 3.61/1.01  --comb_sup_mult                         2
% 3.61/1.01  --comb_inst_mult                        10
% 3.61/1.01  
% 3.61/1.01  ------ Debug Options
% 3.61/1.01  
% 3.61/1.01  --dbg_backtrace                         false
% 3.61/1.01  --dbg_dump_prop_clauses                 false
% 3.61/1.01  --dbg_dump_prop_clauses_file            -
% 3.61/1.01  --dbg_out_stat                          false
% 3.61/1.01  
% 3.61/1.01  
% 3.61/1.01  
% 3.61/1.01  
% 3.61/1.01  ------ Proving...
% 3.61/1.01  
% 3.61/1.01  
% 3.61/1.01  % SZS status Theorem for theBenchmark.p
% 3.61/1.01  
% 3.61/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.61/1.01  
% 3.61/1.01  fof(f3,axiom,(
% 3.61/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 3.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f19,plain,(
% 3.61/1.01    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.61/1.01    inference(ennf_transformation,[],[f3])).
% 3.61/1.01  
% 3.61/1.01  fof(f20,plain,(
% 3.61/1.01    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.61/1.01    inference(flattening,[],[f19])).
% 3.61/1.01  
% 3.61/1.01  fof(f42,plain,(
% 3.61/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),X0)))),
% 3.61/1.01    introduced(choice_axiom,[])).
% 3.61/1.01  
% 3.61/1.01  fof(f43,plain,(
% 3.61/1.01    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.61/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f42])).
% 3.61/1.01  
% 3.61/1.01  fof(f67,plain,(
% 3.61/1.01    ( ! [X0,X1] : (X0 = X1 | m1_subset_1(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/1.01    inference(cnf_transformation,[],[f43])).
% 3.61/1.01  
% 3.61/1.01  fof(f6,axiom,(
% 3.61/1.01    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 3.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f25,plain,(
% 3.61/1.01    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.61/1.01    inference(ennf_transformation,[],[f6])).
% 3.61/1.01  
% 3.61/1.01  fof(f26,plain,(
% 3.61/1.01    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.61/1.01    inference(flattening,[],[f25])).
% 3.61/1.01  
% 3.61/1.01  fof(f44,plain,(
% 3.61/1.01    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.61/1.01    inference(nnf_transformation,[],[f26])).
% 3.61/1.01  
% 3.61/1.01  fof(f45,plain,(
% 3.61/1.01    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.61/1.01    inference(rectify,[],[f44])).
% 3.61/1.01  
% 3.61/1.01  fof(f46,plain,(
% 3.61/1.01    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 3.61/1.01    introduced(choice_axiom,[])).
% 3.61/1.01  
% 3.61/1.01  fof(f47,plain,(
% 3.61/1.01    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.61/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).
% 3.61/1.01  
% 3.61/1.01  fof(f73,plain,(
% 3.61/1.01    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f47])).
% 3.61/1.01  
% 3.61/1.01  fof(f13,conjecture,(
% 3.61/1.01    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f14,negated_conjecture,(
% 3.61/1.01    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.61/1.01    inference(negated_conjecture,[],[f13])).
% 3.61/1.01  
% 3.61/1.01  fof(f15,plain,(
% 3.61/1.01    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.61/1.01    inference(pure_predicate_removal,[],[f14])).
% 3.61/1.01  
% 3.61/1.01  fof(f16,plain,(
% 3.61/1.01    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.61/1.01    inference(pure_predicate_removal,[],[f15])).
% 3.61/1.01  
% 3.61/1.01  fof(f17,plain,(
% 3.61/1.01    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.61/1.01    inference(pure_predicate_removal,[],[f16])).
% 3.61/1.01  
% 3.61/1.01  fof(f36,plain,(
% 3.61/1.01    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.61/1.01    inference(ennf_transformation,[],[f17])).
% 3.61/1.01  
% 3.61/1.01  fof(f37,plain,(
% 3.61/1.01    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.61/1.01    inference(flattening,[],[f36])).
% 3.61/1.01  
% 3.61/1.01  fof(f59,plain,(
% 3.61/1.01    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.61/1.01    inference(nnf_transformation,[],[f37])).
% 3.61/1.01  
% 3.61/1.01  fof(f60,plain,(
% 3.61/1.01    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.61/1.01    inference(flattening,[],[f59])).
% 3.61/1.01  
% 3.61/1.01  fof(f62,plain,(
% 3.61/1.01    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK7) | ~v1_subset_1(sK7,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK7) | v1_subset_1(sK7,u1_struct_0(X0))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK7,X0) & ~v1_xboole_0(sK7))) )),
% 3.61/1.01    introduced(choice_axiom,[])).
% 3.61/1.01  
% 3.61/1.01  fof(f61,plain,(
% 3.61/1.01    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK6),X1) | ~v1_subset_1(X1,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),X1) | v1_subset_1(X1,u1_struct_0(sK6))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(X1,sK6) & ~v1_xboole_0(X1)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & ~v2_struct_0(sK6))),
% 3.61/1.01    introduced(choice_axiom,[])).
% 3.61/1.01  
% 3.61/1.01  fof(f63,plain,(
% 3.61/1.01    ((r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(sK7,sK6) & ~v1_xboole_0(sK7)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & ~v2_struct_0(sK6)),
% 3.61/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f60,f62,f61])).
% 3.61/1.01  
% 3.61/1.01  fof(f94,plain,(
% 3.61/1.01    l1_orders_2(sK6)),
% 3.61/1.01    inference(cnf_transformation,[],[f63])).
% 3.61/1.01  
% 3.61/1.01  fof(f72,plain,(
% 3.61/1.01    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f47])).
% 3.61/1.01  
% 3.61/1.01  fof(f71,plain,(
% 3.61/1.01    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f47])).
% 3.61/1.01  
% 3.61/1.01  fof(f97,plain,(
% 3.61/1.01    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 3.61/1.01    inference(cnf_transformation,[],[f63])).
% 3.61/1.01  
% 3.61/1.01  fof(f11,axiom,(
% 3.61/1.01    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 3.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f33,plain,(
% 3.61/1.01    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.61/1.01    inference(ennf_transformation,[],[f11])).
% 3.61/1.01  
% 3.61/1.01  fof(f34,plain,(
% 3.61/1.01    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.61/1.01    inference(flattening,[],[f33])).
% 3.61/1.01  
% 3.61/1.01  fof(f53,plain,(
% 3.61/1.01    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.61/1.01    inference(nnf_transformation,[],[f34])).
% 3.61/1.01  
% 3.61/1.01  fof(f54,plain,(
% 3.61/1.01    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.61/1.01    inference(rectify,[],[f53])).
% 3.61/1.01  
% 3.61/1.01  fof(f56,plain,(
% 3.61/1.01    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,X2,sK5(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))) )),
% 3.61/1.01    introduced(choice_axiom,[])).
% 3.61/1.01  
% 3.61/1.01  fof(f55,plain,(
% 3.61/1.01    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 3.61/1.01    introduced(choice_axiom,[])).
% 3.61/1.01  
% 3.61/1.01  fof(f57,plain,(
% 3.61/1.01    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.61/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f54,f56,f55])).
% 3.61/1.01  
% 3.61/1.01  fof(f83,plain,(
% 3.61/1.01    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f57])).
% 3.61/1.01  
% 3.61/1.01  fof(f5,axiom,(
% 3.61/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f23,plain,(
% 3.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.61/1.01    inference(ennf_transformation,[],[f5])).
% 3.61/1.01  
% 3.61/1.01  fof(f24,plain,(
% 3.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.61/1.01    inference(flattening,[],[f23])).
% 3.61/1.01  
% 3.61/1.01  fof(f70,plain,(
% 3.61/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f24])).
% 3.61/1.01  
% 3.61/1.01  fof(f96,plain,(
% 3.61/1.01    v13_waybel_0(sK7,sK6)),
% 3.61/1.01    inference(cnf_transformation,[],[f63])).
% 3.61/1.01  
% 3.61/1.01  fof(f95,plain,(
% 3.61/1.01    ~v1_xboole_0(sK7)),
% 3.61/1.01    inference(cnf_transformation,[],[f63])).
% 3.61/1.01  
% 3.61/1.01  fof(f7,axiom,(
% 3.61/1.01    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 3.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f27,plain,(
% 3.61/1.01    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 3.61/1.01    inference(ennf_transformation,[],[f7])).
% 3.61/1.01  
% 3.61/1.01  fof(f75,plain,(
% 3.61/1.01    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f27])).
% 3.61/1.01  
% 3.61/1.01  fof(f9,axiom,(
% 3.61/1.01    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 3.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f30,plain,(
% 3.61/1.01    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.61/1.01    inference(ennf_transformation,[],[f9])).
% 3.61/1.01  
% 3.61/1.01  fof(f81,plain,(
% 3.61/1.01    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f30])).
% 3.61/1.01  
% 3.61/1.01  fof(f8,axiom,(
% 3.61/1.01    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 3.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f28,plain,(
% 3.61/1.01    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.61/1.01    inference(ennf_transformation,[],[f8])).
% 3.61/1.01  
% 3.61/1.01  fof(f29,plain,(
% 3.61/1.01    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.61/1.01    inference(flattening,[],[f28])).
% 3.61/1.01  
% 3.61/1.01  fof(f48,plain,(
% 3.61/1.01    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.61/1.01    inference(nnf_transformation,[],[f29])).
% 3.61/1.01  
% 3.61/1.01  fof(f49,plain,(
% 3.61/1.01    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.61/1.01    inference(flattening,[],[f48])).
% 3.61/1.01  
% 3.61/1.01  fof(f50,plain,(
% 3.61/1.01    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.61/1.01    inference(rectify,[],[f49])).
% 3.61/1.01  
% 3.61/1.01  fof(f51,plain,(
% 3.61/1.01    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) & r2_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 3.61/1.01    introduced(choice_axiom,[])).
% 3.61/1.01  
% 3.61/1.01  fof(f52,plain,(
% 3.61/1.01    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) & r2_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.61/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).
% 3.61/1.01  
% 3.61/1.01  fof(f77,plain,(
% 3.61/1.01    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f52])).
% 3.61/1.01  
% 3.61/1.01  fof(f100,plain,(
% 3.61/1.01    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.61/1.01    inference(equality_resolution,[],[f77])).
% 3.61/1.01  
% 3.61/1.01  fof(f10,axiom,(
% 3.61/1.01    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 3.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f18,plain,(
% 3.61/1.01    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 3.61/1.01    inference(pure_predicate_removal,[],[f10])).
% 3.61/1.01  
% 3.61/1.01  fof(f31,plain,(
% 3.61/1.01    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.61/1.01    inference(ennf_transformation,[],[f18])).
% 3.61/1.01  
% 3.61/1.01  fof(f32,plain,(
% 3.61/1.01    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.61/1.01    inference(flattening,[],[f31])).
% 3.61/1.01  
% 3.61/1.01  fof(f82,plain,(
% 3.61/1.01    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f32])).
% 3.61/1.01  
% 3.61/1.01  fof(f93,plain,(
% 3.61/1.01    v1_yellow_0(sK6)),
% 3.61/1.01    inference(cnf_transformation,[],[f63])).
% 3.61/1.01  
% 3.61/1.01  fof(f91,plain,(
% 3.61/1.01    ~v2_struct_0(sK6)),
% 3.61/1.01    inference(cnf_transformation,[],[f63])).
% 3.61/1.01  
% 3.61/1.01  fof(f92,plain,(
% 3.61/1.01    v5_orders_2(sK6)),
% 3.61/1.01    inference(cnf_transformation,[],[f63])).
% 3.61/1.01  
% 3.61/1.01  fof(f76,plain,(
% 3.61/1.01    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f52])).
% 3.61/1.01  
% 3.61/1.01  fof(f101,plain,(
% 3.61/1.01    ( ! [X0,X1] : (r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.61/1.01    inference(equality_resolution,[],[f76])).
% 3.61/1.01  
% 3.61/1.01  fof(f1,axiom,(
% 3.61/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f38,plain,(
% 3.61/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.61/1.01    inference(nnf_transformation,[],[f1])).
% 3.61/1.01  
% 3.61/1.01  fof(f39,plain,(
% 3.61/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.61/1.01    inference(rectify,[],[f38])).
% 3.61/1.01  
% 3.61/1.01  fof(f40,plain,(
% 3.61/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.61/1.01    introduced(choice_axiom,[])).
% 3.61/1.01  
% 3.61/1.01  fof(f41,plain,(
% 3.61/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.61/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 3.61/1.01  
% 3.61/1.01  fof(f64,plain,(
% 3.61/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f41])).
% 3.61/1.01  
% 3.61/1.01  fof(f2,axiom,(
% 3.61/1.01    v1_xboole_0(k1_xboole_0)),
% 3.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f66,plain,(
% 3.61/1.01    v1_xboole_0(k1_xboole_0)),
% 3.61/1.01    inference(cnf_transformation,[],[f2])).
% 3.61/1.01  
% 3.61/1.01  fof(f12,axiom,(
% 3.61/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f35,plain,(
% 3.61/1.01    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.61/1.01    inference(ennf_transformation,[],[f12])).
% 3.61/1.01  
% 3.61/1.01  fof(f58,plain,(
% 3.61/1.01    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.61/1.01    inference(nnf_transformation,[],[f35])).
% 3.61/1.01  
% 3.61/1.01  fof(f90,plain,(
% 3.61/1.01    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/1.01    inference(cnf_transformation,[],[f58])).
% 3.61/1.01  
% 3.61/1.01  fof(f99,plain,(
% 3.61/1.01    r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))),
% 3.61/1.01    inference(cnf_transformation,[],[f63])).
% 3.61/1.01  
% 3.61/1.01  fof(f4,axiom,(
% 3.61/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/1.01  
% 3.61/1.01  fof(f21,plain,(
% 3.61/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.61/1.01    inference(ennf_transformation,[],[f4])).
% 3.61/1.01  
% 3.61/1.01  fof(f22,plain,(
% 3.61/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.61/1.01    inference(flattening,[],[f21])).
% 3.61/1.01  
% 3.61/1.01  fof(f69,plain,(
% 3.61/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.61/1.01    inference(cnf_transformation,[],[f22])).
% 3.61/1.01  
% 3.61/1.01  fof(f68,plain,(
% 3.61/1.01    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/1.01    inference(cnf_transformation,[],[f43])).
% 3.61/1.01  
% 3.61/1.01  fof(f89,plain,(
% 3.61/1.01    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/1.01    inference(cnf_transformation,[],[f58])).
% 3.61/1.01  
% 3.61/1.01  fof(f102,plain,(
% 3.61/1.01    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 3.61/1.01    inference(equality_resolution,[],[f89])).
% 3.61/1.01  
% 3.61/1.01  fof(f98,plain,(
% 3.61/1.01    ~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))),
% 3.61/1.01    inference(cnf_transformation,[],[f63])).
% 3.61/1.01  
% 3.61/1.01  cnf(c_4,plain,
% 3.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.61/1.01      | m1_subset_1(sK1(X1,X0),X1)
% 3.61/1.01      | X0 = X1 ),
% 3.61/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2503,plain,
% 3.61/1.01      ( X0 = X1
% 3.61/1.01      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.61/1.01      | m1_subset_1(sK1(X1,X0),X1) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_8,plain,
% 3.61/1.01      ( r2_lattice3(X0,X1,X2)
% 3.61/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.61/1.01      | r2_hidden(sK2(X0,X1,X2),X1)
% 3.61/1.01      | ~ l1_orders_2(X0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_32,negated_conjecture,
% 3.61/1.01      ( l1_orders_2(sK6) ),
% 3.61/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_819,plain,
% 3.61/1.01      ( r2_lattice3(X0,X1,X2)
% 3.61/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.61/1.01      | r2_hidden(sK2(X0,X1,X2),X1)
% 3.61/1.01      | sK6 != X0 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_32]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_820,plain,
% 3.61/1.01      ( r2_lattice3(sK6,X0,X1)
% 3.61/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.61/1.01      | r2_hidden(sK2(sK6,X0,X1),X0) ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_819]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2485,plain,
% 3.61/1.01      ( r2_lattice3(sK6,X0,X1) = iProver_top
% 3.61/1.01      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | r2_hidden(sK2(sK6,X0,X1),X0) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_820]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_9,plain,
% 3.61/1.01      ( r2_lattice3(X0,X1,X2)
% 3.61/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.61/1.01      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 3.61/1.01      | ~ l1_orders_2(X0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_804,plain,
% 3.61/1.01      ( r2_lattice3(X0,X1,X2)
% 3.61/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.61/1.01      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 3.61/1.01      | sK6 != X0 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_32]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_805,plain,
% 3.61/1.01      ( r2_lattice3(sK6,X0,X1)
% 3.61/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.61/1.01      | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6)) ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_804]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2486,plain,
% 3.61/1.01      ( r2_lattice3(sK6,X0,X1) = iProver_top
% 3.61/1.01      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6)) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_805]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_10,plain,
% 3.61/1.01      ( r1_orders_2(X0,X1,X2)
% 3.61/1.01      | ~ r2_lattice3(X0,X3,X2)
% 3.61/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.61/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.61/1.01      | ~ r2_hidden(X1,X3)
% 3.61/1.01      | ~ l1_orders_2(X0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_783,plain,
% 3.61/1.01      ( r1_orders_2(X0,X1,X2)
% 3.61/1.01      | ~ r2_lattice3(X0,X3,X2)
% 3.61/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.61/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.61/1.01      | ~ r2_hidden(X1,X3)
% 3.61/1.01      | sK6 != X0 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_32]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_784,plain,
% 3.61/1.01      ( r1_orders_2(sK6,X0,X1)
% 3.61/1.01      | ~ r2_lattice3(sK6,X2,X1)
% 3.61/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.61/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.61/1.01      | ~ r2_hidden(X0,X2) ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_783]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2487,plain,
% 3.61/1.01      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 3.61/1.01      | r2_lattice3(sK6,X2,X1) != iProver_top
% 3.61/1.01      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | r2_hidden(X0,X2) != iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_784]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3529,plain,
% 3.61/1.01      ( r1_orders_2(sK6,sK2(sK6,X0,X1),X2) = iProver_top
% 3.61/1.01      | r2_lattice3(sK6,X3,X2) != iProver_top
% 3.61/1.01      | r2_lattice3(sK6,X0,X1) = iProver_top
% 3.61/1.01      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | r2_hidden(sK2(sK6,X0,X1),X3) != iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_2486,c_2487]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_6333,plain,
% 3.61/1.01      ( r1_orders_2(sK6,sK2(sK6,X0,X1),X2) = iProver_top
% 3.61/1.01      | r2_lattice3(sK6,X0,X2) != iProver_top
% 3.61/1.01      | r2_lattice3(sK6,X0,X1) = iProver_top
% 3.61/1.01      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_2485,c_3529]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_29,negated_conjecture,
% 3.61/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.61/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2500,plain,
% 3.61/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_24,plain,
% 3.61/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 3.61/1.01      | ~ v13_waybel_0(X3,X0)
% 3.61/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.61/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.61/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.61/1.01      | ~ r2_hidden(X1,X3)
% 3.61/1.01      | r2_hidden(X2,X3)
% 3.61/1.01      | ~ l1_orders_2(X0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_729,plain,
% 3.61/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 3.61/1.01      | ~ v13_waybel_0(X3,X0)
% 3.61/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.61/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.61/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.61/1.01      | ~ r2_hidden(X1,X3)
% 3.61/1.01      | r2_hidden(X2,X3)
% 3.61/1.01      | sK6 != X0 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_730,plain,
% 3.61/1.01      ( ~ r1_orders_2(sK6,X0,X1)
% 3.61/1.01      | ~ v13_waybel_0(X2,sK6)
% 3.61/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.61/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.61/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.61/1.01      | ~ r2_hidden(X0,X2)
% 3.61/1.01      | r2_hidden(X1,X2) ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_729]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_6,plain,
% 3.61/1.01      ( m1_subset_1(X0,X1)
% 3.61/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.61/1.01      | ~ r2_hidden(X0,X2) ),
% 3.61/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_746,plain,
% 3.61/1.01      ( ~ r1_orders_2(sK6,X0,X1)
% 3.61/1.01      | ~ v13_waybel_0(X2,sK6)
% 3.61/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.61/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.61/1.01      | ~ r2_hidden(X0,X2)
% 3.61/1.01      | r2_hidden(X1,X2) ),
% 3.61/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_730,c_6]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2490,plain,
% 3.61/1.01      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.61/1.01      | v13_waybel_0(X2,sK6) != iProver_top
% 3.61/1.01      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.61/1.01      | r2_hidden(X0,X2) != iProver_top
% 3.61/1.01      | r2_hidden(X1,X2) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_746]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3985,plain,
% 3.61/1.01      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.61/1.01      | v13_waybel_0(sK7,sK6) != iProver_top
% 3.61/1.01      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | r2_hidden(X0,sK7) != iProver_top
% 3.61/1.01      | r2_hidden(X1,sK7) = iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_2500,c_2490]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_30,negated_conjecture,
% 3.61/1.01      ( v13_waybel_0(sK7,sK6) ),
% 3.61/1.01      inference(cnf_transformation,[],[f96]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_957,plain,
% 3.61/1.01      ( ~ r1_orders_2(sK6,X0,X1)
% 3.61/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.61/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.61/1.01      | ~ r2_hidden(X0,X2)
% 3.61/1.01      | r2_hidden(X1,X2)
% 3.61/1.01      | sK7 != X2
% 3.61/1.01      | sK6 != sK6 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_30,c_746]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_958,plain,
% 3.61/1.01      ( ~ r1_orders_2(sK6,X0,X1)
% 3.61/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.61/1.01      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.61/1.01      | ~ r2_hidden(X0,sK7)
% 3.61/1.01      | r2_hidden(X1,sK7) ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_957]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_960,plain,
% 3.61/1.01      ( ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.61/1.01      | ~ r1_orders_2(sK6,X0,X1)
% 3.61/1.01      | ~ r2_hidden(X0,sK7)
% 3.61/1.01      | r2_hidden(X1,sK7) ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_958,c_29]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_961,plain,
% 3.61/1.01      ( ~ r1_orders_2(sK6,X0,X1)
% 3.61/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.61/1.01      | ~ r2_hidden(X0,sK7)
% 3.61/1.01      | r2_hidden(X1,sK7) ),
% 3.61/1.01      inference(renaming,[status(thm)],[c_960]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_962,plain,
% 3.61/1.01      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.61/1.01      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | r2_hidden(X0,sK7) != iProver_top
% 3.61/1.01      | r2_hidden(X1,sK7) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_961]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_4129,plain,
% 3.61/1.01      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.61/1.01      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | r2_hidden(X0,sK7) != iProver_top
% 3.61/1.01      | r2_hidden(X1,sK7) = iProver_top ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_3985,c_962]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_6679,plain,
% 3.61/1.01      ( r2_lattice3(sK6,X0,X1) != iProver_top
% 3.61/1.01      | r2_lattice3(sK6,X0,X2) = iProver_top
% 3.61/1.01      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | r2_hidden(X1,sK7) = iProver_top
% 3.61/1.01      | r2_hidden(sK2(sK6,X0,X2),sK7) != iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_6333,c_4129]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_6686,plain,
% 3.61/1.01      ( r2_lattice3(sK6,sK7,X0) != iProver_top
% 3.61/1.01      | r2_lattice3(sK6,sK7,X1) = iProver_top
% 3.61/1.01      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | r2_hidden(X0,sK7) = iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_2485,c_6679]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_31,negated_conjecture,
% 3.61/1.01      ( ~ v1_xboole_0(sK7) ),
% 3.61/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_40,plain,
% 3.61/1.01      ( v1_xboole_0(sK7) != iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1997,plain,
% 3.61/1.01      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 3.61/1.01      theory(equality) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2011,plain,
% 3.61/1.01      ( k3_yellow_0(sK6) = k3_yellow_0(sK6) | sK6 != sK6 ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_1997]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1987,plain,( X0 = X0 ),theory(equality) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2018,plain,
% 3.61/1.01      ( sK6 = sK6 ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_1987]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_11,plain,
% 3.61/1.01      ( ~ l1_orders_2(X0)
% 3.61/1.01      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_778,plain,
% 3.61/1.01      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK6 != X0 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_32]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_779,plain,
% 3.61/1.01      ( k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_778]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_17,plain,
% 3.61/1.01      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.61/1.01      | ~ l1_orders_2(X0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_769,plain,
% 3.61/1.01      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK6 != X0 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_32]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_770,plain,
% 3.61/1.01      ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_769]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2488,plain,
% 3.61/1.01      ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_770]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2756,plain,
% 3.61/1.01      ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_779,c_2488]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3019,plain,
% 3.61/1.01      ( sK7 = sK7 ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_1987]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1992,plain,
% 3.61/1.01      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.61/1.01      theory(equality) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2685,plain,
% 3.61/1.01      ( ~ m1_subset_1(X0,X1)
% 3.61/1.01      | m1_subset_1(X2,sK7)
% 3.61/1.01      | X2 != X0
% 3.61/1.01      | sK7 != X1 ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_1992]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2888,plain,
% 3.61/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.61/1.01      | m1_subset_1(X1,sK7)
% 3.61/1.01      | X1 != X0
% 3.61/1.01      | sK7 != u1_struct_0(sK6) ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_2685]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3052,plain,
% 3.61/1.01      ( m1_subset_1(X0,sK7)
% 3.61/1.01      | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
% 3.61/1.01      | X0 != k3_yellow_0(sK6)
% 3.61/1.01      | sK7 != u1_struct_0(sK6) ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_2888]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3834,plain,
% 3.61/1.01      ( ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
% 3.61/1.01      | m1_subset_1(k3_yellow_0(sK6),sK7)
% 3.61/1.01      | k3_yellow_0(sK6) != k3_yellow_0(sK6)
% 3.61/1.01      | sK7 != u1_struct_0(sK6) ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_3052]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3835,plain,
% 3.61/1.01      ( k3_yellow_0(sK6) != k3_yellow_0(sK6)
% 3.61/1.01      | sK7 != u1_struct_0(sK6)
% 3.61/1.01      | m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | m1_subset_1(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_3834]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_15,plain,
% 3.61/1.01      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.61/1.01      | ~ r2_lattice3(X0,X1,X2)
% 3.61/1.01      | ~ r1_yellow_0(X0,X1)
% 3.61/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.61/1.01      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.61/1.01      | ~ l1_orders_2(X0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f100]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_221,plain,
% 3.61/1.01      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.61/1.01      | ~ r1_yellow_0(X0,X1)
% 3.61/1.01      | ~ r2_lattice3(X0,X1,X2)
% 3.61/1.01      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.61/1.01      | ~ l1_orders_2(X0) ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_15,c_17]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_222,plain,
% 3.61/1.01      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.61/1.01      | ~ r2_lattice3(X0,X1,X2)
% 3.61/1.01      | ~ r1_yellow_0(X0,X1)
% 3.61/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.61/1.01      | ~ l1_orders_2(X0) ),
% 3.61/1.01      inference(renaming,[status(thm)],[c_221]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_18,plain,
% 3.61/1.01      ( r1_yellow_0(X0,k1_xboole_0)
% 3.61/1.01      | v2_struct_0(X0)
% 3.61/1.01      | ~ v5_orders_2(X0)
% 3.61/1.01      | ~ v1_yellow_0(X0)
% 3.61/1.01      | ~ l1_orders_2(X0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_33,negated_conjecture,
% 3.61/1.01      ( v1_yellow_0(sK6) ),
% 3.61/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_488,plain,
% 3.61/1.01      ( r1_yellow_0(X0,k1_xboole_0)
% 3.61/1.01      | v2_struct_0(X0)
% 3.61/1.01      | ~ v5_orders_2(X0)
% 3.61/1.01      | ~ l1_orders_2(X0)
% 3.61/1.01      | sK6 != X0 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_33]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_489,plain,
% 3.61/1.01      ( r1_yellow_0(sK6,k1_xboole_0)
% 3.61/1.01      | v2_struct_0(sK6)
% 3.61/1.01      | ~ v5_orders_2(sK6)
% 3.61/1.01      | ~ l1_orders_2(sK6) ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_488]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_35,negated_conjecture,
% 3.61/1.01      ( ~ v2_struct_0(sK6) ),
% 3.61/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_34,negated_conjecture,
% 3.61/1.01      ( v5_orders_2(sK6) ),
% 3.61/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_68,plain,
% 3.61/1.01      ( r1_yellow_0(sK6,k1_xboole_0)
% 3.61/1.01      | v2_struct_0(sK6)
% 3.61/1.01      | ~ v5_orders_2(sK6)
% 3.61/1.01      | ~ v1_yellow_0(sK6)
% 3.61/1.01      | ~ l1_orders_2(sK6) ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_491,plain,
% 3.61/1.01      ( r1_yellow_0(sK6,k1_xboole_0) ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_489,c_35,c_34,c_33,c_32,c_68]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_628,plain,
% 3.61/1.01      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.61/1.01      | ~ r2_lattice3(X0,X1,X2)
% 3.61/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.61/1.01      | ~ l1_orders_2(X0)
% 3.61/1.01      | sK6 != X0
% 3.61/1.01      | k1_xboole_0 != X1 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_222,c_491]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_629,plain,
% 3.61/1.01      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
% 3.61/1.01      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 3.61/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.61/1.01      | ~ l1_orders_2(sK6) ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_628]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_633,plain,
% 3.61/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.61/1.01      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 3.61/1.01      | r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_629,c_32]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_634,plain,
% 3.61/1.01      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
% 3.61/1.01      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 3.61/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 3.61/1.01      inference(renaming,[status(thm)],[c_633]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2494,plain,
% 3.61/1.01      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) = iProver_top
% 3.61/1.01      | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 3.61/1.01      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2509,plain,
% 3.61/1.01      ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
% 3.61/1.01      | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 3.61/1.01      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.61/1.01      inference(light_normalisation,[status(thm)],[c_2494,c_779]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_4134,plain,
% 3.61/1.01      ( r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 3.61/1.01      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | r2_hidden(X0,sK7) = iProver_top
% 3.61/1.01      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_2509,c_4129]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_16,plain,
% 3.61/1.01      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 3.61/1.01      | ~ r1_yellow_0(X0,X1)
% 3.61/1.01      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.61/1.01      | ~ l1_orders_2(X0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f101]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_214,plain,
% 3.61/1.01      ( ~ r1_yellow_0(X0,X1)
% 3.61/1.01      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 3.61/1.01      | ~ l1_orders_2(X0) ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_16,c_17]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_215,plain,
% 3.61/1.01      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 3.61/1.01      | ~ r1_yellow_0(X0,X1)
% 3.61/1.01      | ~ l1_orders_2(X0) ),
% 3.61/1.01      inference(renaming,[status(thm)],[c_214]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_649,plain,
% 3.61/1.01      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 3.61/1.01      | ~ l1_orders_2(X0)
% 3.61/1.01      | sK6 != X0
% 3.61/1.01      | k1_xboole_0 != X1 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_215,c_491]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_650,plain,
% 3.61/1.01      ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0))
% 3.61/1.01      | ~ l1_orders_2(sK6) ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_649]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_652,plain,
% 3.61/1.01      ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0)) ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_650,c_32]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2493,plain,
% 3.61/1.01      ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0)) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_652]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2508,plain,
% 3.61/1.01      ( r2_lattice3(sK6,k1_xboole_0,k3_yellow_0(sK6)) = iProver_top ),
% 3.61/1.01      inference(light_normalisation,[status(thm)],[c_2493,c_779]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2501,plain,
% 3.61/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 3.61/1.01      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.61/1.01      | r2_hidden(X0,X2) != iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3599,plain,
% 3.61/1.01      ( m1_subset_1(X0,u1_struct_0(sK6)) = iProver_top
% 3.61/1.01      | r2_hidden(X0,sK7) != iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_2500,c_2501]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3699,plain,
% 3.61/1.01      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 3.61/1.01      | r2_lattice3(sK6,X2,X1) != iProver_top
% 3.61/1.01      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | r2_hidden(X0,X2) != iProver_top
% 3.61/1.01      | r2_hidden(X0,sK7) != iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_3599,c_2487]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_4482,plain,
% 3.61/1.01      ( r1_orders_2(sK6,X0,k3_yellow_0(sK6)) = iProver_top
% 3.61/1.01      | r2_lattice3(sK6,X1,k3_yellow_0(sK6)) != iProver_top
% 3.61/1.01      | r2_hidden(X0,X1) != iProver_top
% 3.61/1.01      | r2_hidden(X0,sK7) != iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_2756,c_3699]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_4693,plain,
% 3.61/1.01      ( r1_orders_2(sK6,X0,k3_yellow_0(sK6)) = iProver_top
% 3.61/1.01      | r2_hidden(X0,sK7) != iProver_top
% 3.61/1.01      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_2508,c_4482]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1,plain,
% 3.61/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.61/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2,plain,
% 3.61/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.61/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_532,plain,
% 3.61/1.01      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_533,plain,
% 3.61/1.01      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_532]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_534,plain,
% 3.61/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_533]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_4697,plain,
% 3.61/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_4693,c_534]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_4702,plain,
% 3.61/1.01      ( r2_lattice3(sK6,k1_xboole_0,X0) = iProver_top
% 3.61/1.01      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_2485,c_4697]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_25,plain,
% 3.61/1.01      ( v1_subset_1(X0,X1)
% 3.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.61/1.01      | X0 = X1 ),
% 3.61/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_27,negated_conjecture,
% 3.61/1.01      ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
% 3.61/1.01      | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.61/1.01      inference(cnf_transformation,[],[f99]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_287,plain,
% 3.61/1.01      ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
% 3.61/1.01      | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.61/1.01      inference(prop_impl,[status(thm)],[c_27]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_570,plain,
% 3.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.61/1.01      | r2_hidden(k3_yellow_0(sK6),sK7)
% 3.61/1.01      | X1 = X0
% 3.61/1.01      | u1_struct_0(sK6) != X1
% 3.61/1.01      | sK7 != X0 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_25,c_287]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_571,plain,
% 3.61/1.01      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.61/1.01      | r2_hidden(k3_yellow_0(sK6),sK7)
% 3.61/1.01      | u1_struct_0(sK6) = sK7 ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_570]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_573,plain,
% 3.61/1.01      ( r2_hidden(k3_yellow_0(sK6),sK7) | u1_struct_0(sK6) = sK7 ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_571,c_29]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2497,plain,
% 3.61/1.01      ( u1_struct_0(sK6) = sK7
% 3.61/1.01      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_573]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5037,plain,
% 3.61/1.01      ( u1_struct_0(sK6) = sK7
% 3.61/1.01      | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 3.61/1.01      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | r2_hidden(X0,sK7) = iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_2497,c_4134]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_1988,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2668,plain,
% 3.61/1.01      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_1988]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2735,plain,
% 3.61/1.01      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_2668]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5119,plain,
% 3.61/1.01      ( u1_struct_0(sK6) != sK7 | sK7 = u1_struct_0(sK6) | sK7 != sK7 ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_2735]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5,plain,
% 3.61/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.61/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2572,plain,
% 3.61/1.01      ( ~ m1_subset_1(X0,sK7) | r2_hidden(X0,sK7) | v1_xboole_0(sK7) ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5797,plain,
% 3.61/1.01      ( ~ m1_subset_1(k3_yellow_0(sK6),sK7)
% 3.61/1.01      | r2_hidden(k3_yellow_0(sK6),sK7)
% 3.61/1.01      | v1_xboole_0(sK7) ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_2572]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5798,plain,
% 3.61/1.01      ( m1_subset_1(k3_yellow_0(sK6),sK7) != iProver_top
% 3.61/1.01      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
% 3.61/1.01      | v1_xboole_0(sK7) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_5797]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_6756,plain,
% 3.61/1.01      ( m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.61/1.01      | r2_hidden(X0,sK7) = iProver_top ),
% 3.61/1.01      inference(global_propositional_subsumption,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_6686,c_40,c_2011,c_2018,c_2756,c_3019,c_3835,c_4134,
% 3.61/1.01                 c_4702,c_5037,c_5119,c_5798]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_6762,plain,
% 3.61/1.01      ( u1_struct_0(sK6) = X0
% 3.61/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.61/1.01      | r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_2503,c_6756]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3,plain,
% 3.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.61/1.01      | ~ r2_hidden(sK1(X1,X0),X0)
% 3.61/1.01      | X0 = X1 ),
% 3.61/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2504,plain,
% 3.61/1.01      ( X0 = X1
% 3.61/1.01      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.61/1.01      | r2_hidden(sK1(X1,X0),X0) != iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_7076,plain,
% 3.61/1.01      ( u1_struct_0(sK6) = sK7
% 3.61/1.01      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_6762,c_2504]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_6769,plain,
% 3.61/1.01      ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.61/1.01      inference(superposition,[status(thm)],[c_2756,c_6756]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2585,plain,
% 3.61/1.01      ( ~ m1_subset_1(X0,X1)
% 3.61/1.01      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.61/1.01      | X2 != X0
% 3.61/1.01      | k1_zfmisc_1(u1_struct_0(sK6)) != X1 ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_1992]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_2799,plain,
% 3.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.61/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.61/1.01      | X1 != X0
% 3.61/1.01      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_2585]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_4005,plain,
% 3.61/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.61/1.01      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.61/1.01      | X0 != sK7
% 3.61/1.01      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_2799]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5118,plain,
% 3.61/1.01      ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.61/1.01      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.61/1.01      | u1_struct_0(sK6) != sK7
% 3.61/1.01      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_4005]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_5126,plain,
% 3.61/1.01      ( u1_struct_0(sK6) != sK7
% 3.61/1.01      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
% 3.61/1.01      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 3.61/1.01      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_5118]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_3222,plain,
% 3.61/1.01      ( k1_zfmisc_1(u1_struct_0(sK6)) = k1_zfmisc_1(u1_struct_0(sK6)) ),
% 3.61/1.01      inference(instantiation,[status(thm)],[c_1987]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_26,plain,
% 3.61/1.01      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 3.61/1.01      inference(cnf_transformation,[],[f102]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_28,negated_conjecture,
% 3.61/1.01      ( v1_subset_1(sK7,u1_struct_0(sK6))
% 3.61/1.01      | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.61/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_285,plain,
% 3.61/1.01      ( v1_subset_1(sK7,u1_struct_0(sK6))
% 3.61/1.01      | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.61/1.01      inference(prop_impl,[status(thm)],[c_28]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_584,plain,
% 3.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 3.61/1.01      | ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 3.61/1.01      | u1_struct_0(sK6) != X0
% 3.61/1.01      | sK7 != X0 ),
% 3.61/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_285]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_585,plain,
% 3.61/1.01      ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.61/1.01      | ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 3.61/1.01      | sK7 != u1_struct_0(sK6) ),
% 3.61/1.01      inference(unflattening,[status(thm)],[c_584]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_586,plain,
% 3.61/1.01      ( sK7 != u1_struct_0(sK6)
% 3.61/1.01      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.61/1.01      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_585]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(c_42,plain,
% 3.61/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.61/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.61/1.01  
% 3.61/1.01  cnf(contradiction,plain,
% 3.61/1.01      ( $false ),
% 3.61/1.01      inference(minisat,
% 3.61/1.01                [status(thm)],
% 3.61/1.01                [c_7076,c_6769,c_5126,c_5119,c_3222,c_3019,c_586,c_42]) ).
% 3.61/1.01  
% 3.61/1.01  
% 3.61/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.61/1.01  
% 3.61/1.01  ------                               Statistics
% 3.61/1.01  
% 3.61/1.01  ------ General
% 3.61/1.01  
% 3.61/1.01  abstr_ref_over_cycles:                  0
% 3.61/1.01  abstr_ref_under_cycles:                 0
% 3.61/1.01  gc_basic_clause_elim:                   0
% 3.61/1.01  forced_gc_time:                         0
% 3.61/1.01  parsing_time:                           0.01
% 3.61/1.01  unif_index_cands_time:                  0.
% 3.61/1.01  unif_index_add_time:                    0.
% 3.61/1.01  orderings_time:                         0.
% 3.61/1.01  out_proof_time:                         0.015
% 3.61/1.01  total_time:                             0.214
% 3.61/1.01  num_of_symbols:                         56
% 3.61/1.01  num_of_terms:                           6038
% 3.61/1.01  
% 3.61/1.01  ------ Preprocessing
% 3.61/1.01  
% 3.61/1.01  num_of_splits:                          0
% 3.61/1.01  num_of_split_atoms:                     0
% 3.61/1.01  num_of_reused_defs:                     0
% 3.61/1.01  num_eq_ax_congr_red:                    34
% 3.61/1.01  num_of_sem_filtered_clauses:            1
% 3.61/1.01  num_of_subtypes:                        0
% 3.61/1.01  monotx_restored_types:                  0
% 3.61/1.01  sat_num_of_epr_types:                   0
% 3.61/1.01  sat_num_of_non_cyclic_types:            0
% 3.61/1.01  sat_guarded_non_collapsed_types:        0
% 3.61/1.01  num_pure_diseq_elim:                    0
% 3.61/1.01  simp_replaced_by:                       0
% 3.61/1.01  res_preprocessed:                       156
% 3.61/1.01  prep_upred:                             0
% 3.61/1.01  prep_unflattend:                        74
% 3.61/1.01  smt_new_axioms:                         0
% 3.61/1.01  pred_elim_cands:                        6
% 3.61/1.01  pred_elim:                              6
% 3.61/1.01  pred_elim_cl:                           7
% 3.61/1.01  pred_elim_cycles:                       12
% 3.61/1.01  merged_defs:                            2
% 3.61/1.01  merged_defs_ncl:                        0
% 3.61/1.01  bin_hyper_res:                          2
% 3.61/1.01  prep_cycles:                            4
% 3.61/1.01  pred_elim_time:                         0.018
% 3.61/1.01  splitting_time:                         0.
% 3.61/1.01  sem_filter_time:                        0.
% 3.61/1.01  monotx_time:                            0.
% 3.61/1.01  subtype_inf_time:                       0.
% 3.61/1.01  
% 3.61/1.01  ------ Problem properties
% 3.61/1.01  
% 3.61/1.01  clauses:                                29
% 3.61/1.01  conjectures:                            3
% 3.61/1.01  epr:                                    5
% 3.61/1.01  horn:                                   17
% 3.61/1.01  ground:                                 8
% 3.61/1.01  unary:                                  7
% 3.61/1.01  binary:                                 3
% 3.61/1.01  lits:                                   78
% 3.61/1.01  lits_eq:                                8
% 3.61/1.01  fd_pure:                                0
% 3.61/1.01  fd_pseudo:                              0
% 3.61/1.01  fd_cond:                                3
% 3.61/1.01  fd_pseudo_cond:                         2
% 3.61/1.01  ac_symbols:                             0
% 3.61/1.01  
% 3.61/1.01  ------ Propositional Solver
% 3.61/1.01  
% 3.61/1.01  prop_solver_calls:                      31
% 3.61/1.01  prop_fast_solver_calls:                 1579
% 3.61/1.01  smt_solver_calls:                       0
% 3.61/1.01  smt_fast_solver_calls:                  0
% 3.61/1.01  prop_num_of_clauses:                    2765
% 3.61/1.01  prop_preprocess_simplified:             7645
% 3.61/1.01  prop_fo_subsumed:                       31
% 3.61/1.01  prop_solver_time:                       0.
% 3.61/1.01  smt_solver_time:                        0.
% 3.61/1.01  smt_fast_solver_time:                   0.
% 3.61/1.01  prop_fast_solver_time:                  0.
% 3.61/1.01  prop_unsat_core_time:                   0.
% 3.61/1.01  
% 3.61/1.01  ------ QBF
% 3.61/1.01  
% 3.61/1.01  qbf_q_res:                              0
% 3.61/1.01  qbf_num_tautologies:                    0
% 3.61/1.01  qbf_prep_cycles:                        0
% 3.61/1.01  
% 3.61/1.01  ------ BMC1
% 3.61/1.01  
% 3.61/1.01  bmc1_current_bound:                     -1
% 3.61/1.01  bmc1_last_solved_bound:                 -1
% 3.61/1.01  bmc1_unsat_core_size:                   -1
% 3.61/1.01  bmc1_unsat_core_parents_size:           -1
% 3.61/1.01  bmc1_merge_next_fun:                    0
% 3.61/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.61/1.01  
% 3.61/1.01  ------ Instantiation
% 3.61/1.01  
% 3.61/1.01  inst_num_of_clauses:                    715
% 3.61/1.01  inst_num_in_passive:                    265
% 3.61/1.01  inst_num_in_active:                     394
% 3.61/1.01  inst_num_in_unprocessed:                56
% 3.61/1.01  inst_num_of_loops:                      480
% 3.61/1.01  inst_num_of_learning_restarts:          0
% 3.61/1.01  inst_num_moves_active_passive:          81
% 3.61/1.01  inst_lit_activity:                      0
% 3.61/1.01  inst_lit_activity_moves:                0
% 3.61/1.01  inst_num_tautologies:                   0
% 3.61/1.01  inst_num_prop_implied:                  0
% 3.61/1.01  inst_num_existing_simplified:           0
% 3.61/1.01  inst_num_eq_res_simplified:             0
% 3.61/1.01  inst_num_child_elim:                    0
% 3.61/1.01  inst_num_of_dismatching_blockings:      213
% 3.61/1.01  inst_num_of_non_proper_insts:           920
% 3.61/1.01  inst_num_of_duplicates:                 0
% 3.61/1.01  inst_inst_num_from_inst_to_res:         0
% 3.61/1.01  inst_dismatching_checking_time:         0.
% 3.61/1.01  
% 3.61/1.01  ------ Resolution
% 3.61/1.01  
% 3.61/1.01  res_num_of_clauses:                     0
% 3.61/1.01  res_num_in_passive:                     0
% 3.61/1.01  res_num_in_active:                      0
% 3.61/1.01  res_num_of_loops:                       160
% 3.61/1.01  res_forward_subset_subsumed:            129
% 3.61/1.01  res_backward_subset_subsumed:           0
% 3.61/1.01  res_forward_subsumed:                   0
% 3.61/1.01  res_backward_subsumed:                  0
% 3.61/1.01  res_forward_subsumption_resolution:     6
% 3.61/1.01  res_backward_subsumption_resolution:    0
% 3.61/1.01  res_clause_to_clause_subsumption:       552
% 3.61/1.01  res_orphan_elimination:                 0
% 3.61/1.01  res_tautology_del:                      52
% 3.61/1.01  res_num_eq_res_simplified:              0
% 3.61/1.01  res_num_sel_changes:                    0
% 3.61/1.01  res_moves_from_active_to_pass:          0
% 3.61/1.01  
% 3.61/1.01  ------ Superposition
% 3.61/1.01  
% 3.61/1.01  sup_time_total:                         0.
% 3.61/1.01  sup_time_generating:                    0.
% 3.61/1.01  sup_time_sim_full:                      0.
% 3.61/1.01  sup_time_sim_immed:                     0.
% 3.61/1.01  
% 3.61/1.01  sup_num_of_clauses:                     158
% 3.61/1.01  sup_num_in_active:                      90
% 3.61/1.01  sup_num_in_passive:                     68
% 3.61/1.01  sup_num_of_loops:                       95
% 3.61/1.01  sup_fw_superposition:                   132
% 3.61/1.01  sup_bw_superposition:                   101
% 3.61/1.01  sup_immediate_simplified:               65
% 3.61/1.01  sup_given_eliminated:                   0
% 3.61/1.01  comparisons_done:                       0
% 3.61/1.01  comparisons_avoided:                    0
% 3.61/1.01  
% 3.61/1.01  ------ Simplifications
% 3.61/1.01  
% 3.61/1.01  
% 3.61/1.01  sim_fw_subset_subsumed:                 23
% 3.61/1.01  sim_bw_subset_subsumed:                 0
% 3.61/1.01  sim_fw_subsumed:                        39
% 3.61/1.01  sim_bw_subsumed:                        7
% 3.61/1.01  sim_fw_subsumption_res:                 0
% 3.61/1.01  sim_bw_subsumption_res:                 0
% 3.61/1.01  sim_tautology_del:                      10
% 3.61/1.01  sim_eq_tautology_del:                   3
% 3.61/1.01  sim_eq_res_simp:                        0
% 3.61/1.01  sim_fw_demodulated:                     3
% 3.61/1.01  sim_bw_demodulated:                     0
% 3.61/1.01  sim_light_normalised:                   4
% 3.61/1.01  sim_joinable_taut:                      0
% 3.61/1.01  sim_joinable_simp:                      0
% 3.61/1.01  sim_ac_normalised:                      0
% 3.61/1.01  sim_smt_subsumption:                    0
% 3.61/1.01  
%------------------------------------------------------------------------------
