%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1696+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:11 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  193 (6634 expanded)
%              Number of clauses        :  128 (1128 expanded)
%              Number of leaves         :   14 (1651 expanded)
%              Depth                    :   28
%              Number of atoms          : 1087 (61950 expanded)
%              Number of equality atoms :  199 ( 935 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ! [X3] :
          ( X2 = X3
          | ? [X4] :
              ( ~ r1_orders_2(X0,X4,X3)
              & r1_lattice3(X0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r1_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( X2 != X3
            & ! [X4] :
                ( r1_orders_2(X0,X4,X3)
                | ~ r1_lattice3(X0,X1,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r1_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( X2 = X3
            | ? [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( X0 != X3
            & ! [X4] :
                ( r1_orders_2(X1,X4,X3)
                | ~ r1_lattice3(X1,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & r1_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( X0 = X5
            | ? [X6] :
                ( ~ r1_orders_2(X1,X6,X5)
                & r1_lattice3(X1,X2,X6)
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | ~ r1_lattice3(X1,X2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f23])).

fof(f26,plain,(
    ! [X5,X2,X1] :
      ( ? [X6] :
          ( ~ r1_orders_2(X1,X6,X5)
          & r1_lattice3(X1,X2,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK5(X1,X2,X5),X5)
        & r1_lattice3(X1,X2,sK5(X1,X2,X5))
        & m1_subset_1(sK5(X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X0 != X3
          & ! [X4] :
              ( r1_orders_2(X1,X4,X3)
              | ~ r1_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r1_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( sK4(X0,X1,X2) != X0
        & ! [X4] :
            ( r1_orders_2(X1,X4,sK4(X0,X1,X2))
            | ~ r1_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & r1_lattice3(X1,X2,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( sK4(X0,X1,X2) != X0
          & ! [X4] :
              ( r1_orders_2(X1,X4,sK4(X0,X1,X2))
              | ~ r1_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r1_lattice3(X1,X2,sK4(X0,X1,X2))
          & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( X0 = X5
            | ( ~ r1_orders_2(X1,sK5(X1,X2,X5),X5)
              & r1_lattice3(X1,X2,sK5(X1,X2,X5))
              & m1_subset_1(sK5(X1,X2,X5),u1_struct_0(X1)) )
            | ~ r1_lattice3(X1,X2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f26,f25])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_lattice3(X1,X2,sK4(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_orders_2(X1,X4,sK4(X0,X1,X2))
      | ~ r1_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v25_waybel_0(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ? [X2] :
                ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ( v25_waybel_0(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ( v25_waybel_0(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f17,plain,(
    ! [X0] :
      ( ( ( v25_waybel_0(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( ~ r1_orders_2(X0,X3,X2)
                      & r1_lattice3(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( r1_orders_2(X0,X3,X2)
                      | ~ r1_lattice3(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | v1_xboole_0(X1) )
          | ~ v25_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( ( ( v25_waybel_0(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( ~ r1_orders_2(X0,X3,X2)
                      & r1_lattice3(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) ) )
        & ( ! [X4] :
              ( ? [X5] :
                  ( ! [X6] :
                      ( r1_orders_2(X0,X6,X5)
                      | ~ r1_lattice3(X0,X4,X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X4,X5)
                  & m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
              | v1_xboole_0(X4) )
          | ~ v25_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f17])).

fof(f21,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_orders_2(X0,X6,X5)
              | ~ r1_lattice3(X0,X4,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r1_lattice3(X0,X4,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r1_orders_2(X0,X6,sK3(X0,X4))
            | ~ r1_lattice3(X0,X4,X6)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r1_lattice3(X0,X4,sK3(X0,X4))
        & m1_subset_1(sK3(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X2),X2)
        & r1_lattice3(X0,X1,sK2(X0,X2))
        & m1_subset_1(sK2(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ! [X2] :
            ( ? [X3] :
                ( ~ r1_orders_2(X0,X3,X2)
                & r1_lattice3(X0,sK1(X0),X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,sK1(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v25_waybel_0(X0)
          | ( ! [X2] :
                ( ( ~ r1_orders_2(X0,sK2(X0,X2),X2)
                  & r1_lattice3(X0,sK1(X0),sK2(X0,X2))
                  & m1_subset_1(sK2(X0,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,sK1(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(sK1(X0)) ) )
        & ( ! [X4] :
              ( ( ! [X6] :
                    ( r1_orders_2(X0,X6,sK3(X0,X4))
                    | ~ r1_lattice3(X0,X4,X6)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_lattice3(X0,X4,sK3(X0,X4))
                & m1_subset_1(sK3(X0,X4),u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
              | v1_xboole_0(X4) )
          | ~ v25_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f21,f20,f19])).

fof(f41,plain,(
    ! [X6,X4,X0] :
      ( r1_orders_2(X0,X6,sK3(X0,X4))
      | ~ r1_lattice3(X0,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X4)
      | ~ v25_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v25_waybel_0(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => r2_yellow_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v25_waybel_0(X0)
        <=> ! [X1] :
              ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(X1) )
             => r2_yellow_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f13,plain,(
    ? [X0] :
      ( ( v25_waybel_0(X0)
      <~> ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ? [X0] :
      ( ( v25_waybel_0(X0)
      <~> ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        | ~ v25_waybel_0(X0) )
      & ( ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X1) )
        | v25_waybel_0(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f34,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        | ~ v25_waybel_0(X0) )
      & ( ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X1) )
        | v25_waybel_0(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        | ~ v25_waybel_0(X0) )
      & ( ! [X2] :
            ( r2_yellow_0(X0,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X2) )
        | v25_waybel_0(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f34])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ~ r2_yellow_0(X0,sK9)
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ~ r2_yellow_0(X0,X1)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
          | ~ v25_waybel_0(X0) )
        & ( ! [X2] :
              ( r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | v1_xboole_0(X2) )
          | v25_waybel_0(X0) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ? [X1] :
            ( ~ r2_yellow_0(sK8,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
            & ~ v1_xboole_0(X1) )
        | ~ v25_waybel_0(sK8) )
      & ( ! [X2] :
            ( r2_yellow_0(sK8,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
            | v1_xboole_0(X2) )
        | v25_waybel_0(sK8) )
      & l1_orders_2(sK8)
      & v5_orders_2(sK8)
      & v3_orders_2(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ( ~ r2_yellow_0(sK8,sK9)
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
        & ~ v1_xboole_0(sK9) )
      | ~ v25_waybel_0(sK8) )
    & ( ! [X2] :
          ( r2_yellow_0(sK8,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
          | v1_xboole_0(X2) )
      | v25_waybel_0(sK8) )
    & l1_orders_2(sK8)
    & v5_orders_2(sK8)
    & v3_orders_2(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f35,f37,f36])).

fof(f63,plain,(
    v3_orders_2(sK8) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,
    ( ~ v1_xboole_0(sK9)
    | ~ v25_waybel_0(sK8) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v25_waybel_0(sK8) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,(
    v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f38])).

fof(f39,plain,(
    ! [X4,X0] :
      ( m1_subset_1(sK3(X0,X4),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X4)
      | ~ v25_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X2,X0] :
      ( v25_waybel_0(X0)
      | m1_subset_1(sK2(X0,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,sK1(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X2,X0] :
      ( v25_waybel_0(X0)
      | r1_lattice3(X0,sK1(X0),sK2(X0,X2))
      | ~ r1_lattice3(X0,sK1(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X5,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( sP0(X2,X0,X1)
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f10,f15])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ~ sP0(X2,X0,X1)
                | ? [X5] :
                    ( ~ r1_orders_2(X0,X5,X2)
                    & r1_lattice3(X0,X1,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( sP0(X2,X0,X1)
                & ! [X5] :
                    ( r1_orders_2(X0,X5,X2)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ~ sP0(X2,X0,X1)
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( sP0(X4,X0,X1)
                & ! [X5] :
                    ( r1_orders_2(X0,X5,X4)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f28])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( sP0(X4,X0,X1)
          & ! [X5] :
              ( r1_orders_2(X0,X5,X4)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( sP0(sK7(X0,X1),X0,X1)
        & ! [X5] :
            ( r1_orders_2(X0,X5,sK7(X0,X1))
            | ~ r1_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK7(X0,X1))
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ~ sP0(X2,X0,X1)
                | ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK6(X0,X1,X2))
                  & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( sP0(sK7(X0,X1),X0,X1)
              & ! [X5] :
                  ( r1_orders_2(X0,X5,sK7(X0,X1))
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK7(X0,X1))
              & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f29,f31,f30])).

fof(f56,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,X5,sK7(X0,X1))
      | ~ r1_lattice3(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    ! [X2,X0] :
      ( v25_waybel_0(X0)
      | ~ r1_orders_2(X0,sK2(X0,X2),X2)
      | ~ r1_lattice3(X0,sK1(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X2] :
      ( r2_yellow_0(sK8,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
      | v1_xboole_0(X2)
      | v25_waybel_0(sK8) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f42,plain,(
    ! [X0] :
      ( v25_waybel_0(X0)
      | ~ v1_xboole_0(sK1(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0] :
      ( v25_waybel_0(X0)
      | m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,sK7(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X4,X0] :
      ( r1_lattice3(X0,X4,sK3(X0,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X4)
      | ~ v25_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ sP0(X2,X0,X1)
      | r1_lattice3(X0,X1,sK6(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ sP0(X2,X0,X1)
      | ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ sP0(X2,X0,X1)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,
    ( ~ r2_yellow_0(sK8,sK9)
    | ~ v25_waybel_0(sK8) ),
    inference(cnf_transformation,[],[f38])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | sK4(X0,X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_10,plain,
    ( sP0(X0,X1,X2)
    | r1_lattice3(X1,X2,sK4(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4770,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r1_lattice3(X1,X2,sK4(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | r1_orders_2(X1,X3,sK4(X0,X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4771,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r1_lattice3(X1,X2,X3) != iProver_top
    | r1_orders_2(X1,X3,sK4(X0,X1,X2)) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,sK3(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v1_xboole_0(X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v25_waybel_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_29,negated_conjecture,
    ( v3_orders_2(sK8) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_406,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,sK3(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v1_xboole_0(X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v25_waybel_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_29])).

cnf(c_407,plain,
    ( ~ r1_lattice3(sK8,X0,X1)
    | r1_orders_2(sK8,X1,sK3(sK8,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | v1_xboole_0(X0)
    | v2_struct_0(sK8)
    | ~ l1_orders_2(sK8)
    | ~ v25_waybel_0(sK8) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,negated_conjecture,
    ( l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_411,plain,
    ( ~ r1_lattice3(sK8,X0,X1)
    | r1_orders_2(sK8,X1,sK3(sK8,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | v1_xboole_0(X0)
    | ~ v25_waybel_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_407,c_30,c_27])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK9)
    | ~ v25_waybel_0(sK8) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_761,plain,
    ( ~ r1_lattice3(sK8,X0,X1)
    | r1_orders_2(sK8,X1,sK3(sK8,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v25_waybel_0(sK8)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_411,c_25])).

cnf(c_762,plain,
    ( ~ r1_lattice3(sK8,sK9,X0)
    | r1_orders_2(sK8,X0,sK3(sK8,sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v25_waybel_0(sK8) ),
    inference(unflattening,[status(thm)],[c_761])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v25_waybel_0(sK8) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_766,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | r1_orders_2(sK8,X0,sK3(sK8,sK9))
    | ~ r1_lattice3(sK8,sK9,X0)
    | ~ v25_waybel_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_762,c_24])).

cnf(c_767,plain,
    ( ~ r1_lattice3(sK8,sK9,X0)
    | r1_orders_2(sK8,X0,sK3(sK8,sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ v25_waybel_0(sK8) ),
    inference(renaming,[status(thm)],[c_766])).

cnf(c_4750,plain,
    ( r1_lattice3(sK8,sK9,X0) != iProver_top
    | r1_orders_2(sK8,X0,sK3(sK8,sK9)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | v25_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_767])).

cnf(c_22,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_28,negated_conjecture,
    ( v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_349,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X2 = X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_350,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l1_orders_2(sK8)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r1_orders_2(sK8,X1,X0)
    | ~ r1_orders_2(sK8,X0,X1)
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_27])).

cnf(c_355,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_354])).

cnf(c_4763,plain,
    ( X0 = X1
    | r1_orders_2(sK8,X0,X1) != iProver_top
    | r1_orders_2(sK8,X1,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_5487,plain,
    ( sK3(sK8,sK9) = X0
    | r1_lattice3(sK8,sK9,X0) != iProver_top
    | r1_orders_2(sK8,sK3(sK8,sK9),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK3(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | v25_waybel_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4750,c_4763])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v25_waybel_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_536,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v25_waybel_0(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_29])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(sK3(sK8,X0),u1_struct_0(sK8))
    | v1_xboole_0(X0)
    | v2_struct_0(sK8)
    | ~ l1_orders_2(sK8)
    | ~ v25_waybel_0(sK8) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_541,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(sK3(sK8,X0),u1_struct_0(sK8))
    | v1_xboole_0(X0)
    | ~ v25_waybel_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_30,c_27])).

cnf(c_747,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(sK3(sK8,X0),u1_struct_0(sK8))
    | ~ v25_waybel_0(sK8)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_541,c_25])).

cnf(c_748,plain,
    ( m1_subset_1(sK3(sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v25_waybel_0(sK8) ),
    inference(unflattening,[status(thm)],[c_747])).

cnf(c_750,plain,
    ( m1_subset_1(sK3(sK8,sK9),u1_struct_0(sK8))
    | ~ v25_waybel_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_748,c_24])).

cnf(c_752,plain,
    ( m1_subset_1(sK3(sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | v25_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_6159,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r1_orders_2(sK8,sK3(sK8,sK9),X0) != iProver_top
    | r1_lattice3(sK8,sK9,X0) != iProver_top
    | sK3(sK8,sK9) = X0
    | v25_waybel_0(sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5487,c_752])).

cnf(c_6160,plain,
    ( sK3(sK8,sK9) = X0
    | r1_lattice3(sK8,sK9,X0) != iProver_top
    | r1_orders_2(sK8,sK3(sK8,sK9),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | v25_waybel_0(sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_6159])).

cnf(c_6170,plain,
    ( sK4(X0,sK8,X1) = sK3(sK8,sK9)
    | sP0(X0,sK8,X1) = iProver_top
    | r1_lattice3(sK8,X1,sK3(sK8,sK9)) != iProver_top
    | r1_lattice3(sK8,sK9,sK4(X0,sK8,X1)) != iProver_top
    | m1_subset_1(sK4(X0,sK8,X1),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK3(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | v25_waybel_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4771,c_6160])).

cnf(c_2,plain,
    ( ~ r1_lattice3(X0,sK1(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v25_waybel_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_464,plain,
    ( ~ r1_lattice3(X0,sK1(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | v25_waybel_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_29])).

cnf(c_465,plain,
    ( ~ r1_lattice3(sK8,sK1(sK8),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK2(sK8,X0),u1_struct_0(sK8))
    | v2_struct_0(sK8)
    | ~ l1_orders_2(sK8)
    | v25_waybel_0(sK8) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_469,plain,
    ( ~ r1_lattice3(sK8,sK1(sK8),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK2(sK8,X0),u1_struct_0(sK8))
    | v25_waybel_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_465,c_30,c_27])).

cnf(c_4761,plain,
    ( r1_lattice3(sK8,sK1(sK8),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK2(sK8,X0),u1_struct_0(sK8)) = iProver_top
    | v25_waybel_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_469])).

cnf(c_1,plain,
    ( ~ r1_lattice3(X0,sK1(X0),X1)
    | r1_lattice3(X0,sK1(X0),sK2(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v25_waybel_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_488,plain,
    ( ~ r1_lattice3(X0,sK1(X0),X1)
    | r1_lattice3(X0,sK1(X0),sK2(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | v25_waybel_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_29])).

cnf(c_489,plain,
    ( ~ r1_lattice3(sK8,sK1(sK8),X0)
    | r1_lattice3(sK8,sK1(sK8),sK2(sK8,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | v2_struct_0(sK8)
    | ~ l1_orders_2(sK8)
    | v25_waybel_0(sK8) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_493,plain,
    ( ~ r1_lattice3(sK8,sK1(sK8),X0)
    | r1_lattice3(sK8,sK1(sK8),sK2(sK8,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | v25_waybel_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_30,c_27])).

cnf(c_4760,plain,
    ( r1_lattice3(sK8,sK1(sK8),X0) != iProver_top
    | r1_lattice3(sK8,sK1(sK8),sK2(sK8,X0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | v25_waybel_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_493])).

cnf(c_19,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,sK7(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_622,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,sK7(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_623,plain,
    ( ~ r1_lattice3(sK8,X0,X1)
    | r1_orders_2(sK8,X1,sK7(sK8,X0))
    | ~ r2_yellow_0(sK8,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_4756,plain,
    ( r1_lattice3(sK8,X0,X1) != iProver_top
    | r1_orders_2(sK8,X1,sK7(sK8,X0)) = iProver_top
    | r2_yellow_0(sK8,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_623])).

cnf(c_0,plain,
    ( ~ r1_lattice3(X0,sK1(X0),X1)
    | ~ r1_orders_2(X0,sK2(X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v25_waybel_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_512,plain,
    ( ~ r1_lattice3(X0,sK1(X0),X1)
    | ~ r1_orders_2(X0,sK2(X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | v25_waybel_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_29])).

cnf(c_513,plain,
    ( ~ r1_lattice3(sK8,sK1(sK8),X0)
    | ~ r1_orders_2(sK8,sK2(sK8,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | v2_struct_0(sK8)
    | ~ l1_orders_2(sK8)
    | v25_waybel_0(sK8) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_517,plain,
    ( ~ r1_lattice3(sK8,sK1(sK8),X0)
    | ~ r1_orders_2(sK8,sK2(sK8,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | v25_waybel_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_513,c_30,c_27])).

cnf(c_4759,plain,
    ( r1_lattice3(sK8,sK1(sK8),X0) != iProver_top
    | r1_orders_2(sK8,sK2(sK8,X0),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | v25_waybel_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_517])).

cnf(c_5447,plain,
    ( r1_lattice3(sK8,X0,sK2(sK8,sK7(sK8,X0))) != iProver_top
    | r1_lattice3(sK8,sK1(sK8),sK7(sK8,X0)) != iProver_top
    | r2_yellow_0(sK8,X0) != iProver_top
    | m1_subset_1(sK7(sK8,X0),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK2(sK8,sK7(sK8,X0)),u1_struct_0(sK8)) != iProver_top
    | v25_waybel_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_4756,c_4759])).

cnf(c_21,plain,
    ( ~ r2_yellow_0(X0,X1)
    | m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_598,plain,
    ( ~ r2_yellow_0(X0,X1)
    | m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_599,plain,
    ( ~ r2_yellow_0(sK8,X0)
    | m1_subset_1(sK7(sK8,X0),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_600,plain,
    ( r2_yellow_0(sK8,X0) != iProver_top
    | m1_subset_1(sK7(sK8,X0),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_6284,plain,
    ( r2_yellow_0(sK8,X0) != iProver_top
    | r1_lattice3(sK8,sK1(sK8),sK7(sK8,X0)) != iProver_top
    | r1_lattice3(sK8,X0,sK2(sK8,sK7(sK8,X0))) != iProver_top
    | m1_subset_1(sK2(sK8,sK7(sK8,X0)),u1_struct_0(sK8)) != iProver_top
    | v25_waybel_0(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5447,c_600])).

cnf(c_6285,plain,
    ( r1_lattice3(sK8,X0,sK2(sK8,sK7(sK8,X0))) != iProver_top
    | r1_lattice3(sK8,sK1(sK8),sK7(sK8,X0)) != iProver_top
    | r2_yellow_0(sK8,X0) != iProver_top
    | m1_subset_1(sK2(sK8,sK7(sK8,X0)),u1_struct_0(sK8)) != iProver_top
    | v25_waybel_0(sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_6284])).

cnf(c_6295,plain,
    ( r1_lattice3(sK8,sK1(sK8),sK7(sK8,sK1(sK8))) != iProver_top
    | r2_yellow_0(sK8,sK1(sK8)) != iProver_top
    | m1_subset_1(sK7(sK8,sK1(sK8)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK2(sK8,sK7(sK8,sK1(sK8))),u1_struct_0(sK8)) != iProver_top
    | v25_waybel_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_4760,c_6285])).

cnf(c_26,negated_conjecture,
    ( r2_yellow_0(sK8,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | v1_xboole_0(X0)
    | v25_waybel_0(sK8) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(sK1(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v25_waybel_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_436,plain,
    ( ~ v1_xboole_0(sK1(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | v25_waybel_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_29])).

cnf(c_437,plain,
    ( ~ v1_xboole_0(sK1(sK8))
    | v2_struct_0(sK8)
    | ~ l1_orders_2(sK8)
    | v25_waybel_0(sK8) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_439,plain,
    ( ~ v1_xboole_0(sK1(sK8))
    | v25_waybel_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_30,c_27])).

cnf(c_807,plain,
    ( r2_yellow_0(sK8,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | v25_waybel_0(sK8)
    | sK1(sK8) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_439])).

cnf(c_808,plain,
    ( r2_yellow_0(sK8,sK1(sK8))
    | ~ m1_subset_1(sK1(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
    | v25_waybel_0(sK8) ),
    inference(unflattening,[status(thm)],[c_807])).

cnf(c_3,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v25_waybel_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_99,plain,
    ( m1_subset_1(sK1(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
    | v2_struct_0(sK8)
    | ~ v3_orders_2(sK8)
    | ~ l1_orders_2(sK8)
    | v25_waybel_0(sK8) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_810,plain,
    ( r2_yellow_0(sK8,sK1(sK8))
    | v25_waybel_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_808,c_30,c_29,c_27,c_99])).

cnf(c_812,plain,
    ( r2_yellow_0(sK8,sK1(sK8)) = iProver_top
    | v25_waybel_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_810])).

cnf(c_20,plain,
    ( r1_lattice3(X0,X1,sK7(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_610,plain,
    ( r1_lattice3(X0,X1,sK7(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_611,plain,
    ( r1_lattice3(sK8,X0,sK7(sK8,X0))
    | ~ r2_yellow_0(sK8,X0) ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_1666,plain,
    ( r1_lattice3(sK8,X0,sK7(sK8,X0))
    | v25_waybel_0(sK8)
    | sK1(sK8) != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_611,c_810])).

cnf(c_1667,plain,
    ( r1_lattice3(sK8,sK1(sK8),sK7(sK8,sK1(sK8)))
    | v25_waybel_0(sK8) ),
    inference(unflattening,[status(thm)],[c_1666])).

cnf(c_1668,plain,
    ( r1_lattice3(sK8,sK1(sK8),sK7(sK8,sK1(sK8))) = iProver_top
    | v25_waybel_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1667])).

cnf(c_1676,plain,
    ( m1_subset_1(sK7(sK8,X0),u1_struct_0(sK8))
    | v25_waybel_0(sK8)
    | sK1(sK8) != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_599,c_810])).

cnf(c_1677,plain,
    ( m1_subset_1(sK7(sK8,sK1(sK8)),u1_struct_0(sK8))
    | v25_waybel_0(sK8) ),
    inference(unflattening,[status(thm)],[c_1676])).

cnf(c_1678,plain,
    ( m1_subset_1(sK7(sK8,sK1(sK8)),u1_struct_0(sK8)) = iProver_top
    | v25_waybel_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1677])).

cnf(c_6298,plain,
    ( m1_subset_1(sK2(sK8,sK7(sK8,sK1(sK8))),u1_struct_0(sK8)) != iProver_top
    | v25_waybel_0(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6295,c_812,c_1668,c_1678])).

cnf(c_6304,plain,
    ( r1_lattice3(sK8,sK1(sK8),sK7(sK8,sK1(sK8))) != iProver_top
    | m1_subset_1(sK7(sK8,sK1(sK8)),u1_struct_0(sK8)) != iProver_top
    | v25_waybel_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_4761,c_6298])).

cnf(c_6307,plain,
    ( v25_waybel_0(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6304,c_1668,c_1678])).

cnf(c_6547,plain,
    ( sK4(X0,sK8,X1) = sK3(sK8,sK9)
    | sP0(X0,sK8,X1) = iProver_top
    | r1_lattice3(sK8,X1,sK3(sK8,sK9)) != iProver_top
    | r1_lattice3(sK8,sK9,sK4(X0,sK8,X1)) != iProver_top
    | m1_subset_1(sK4(X0,sK8,X1),u1_struct_0(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6170,c_752,c_1668,c_1678,c_6304])).

cnf(c_11,plain,
    ( sP0(X0,X1,X2)
    | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4769,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6558,plain,
    ( sK4(X0,sK8,X1) = sK3(sK8,sK9)
    | sP0(X0,sK8,X1) = iProver_top
    | r1_lattice3(sK8,X1,sK3(sK8,sK9)) != iProver_top
    | r1_lattice3(sK8,sK9,sK4(X0,sK8,X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6547,c_4769])).

cnf(c_6562,plain,
    ( sK4(X0,sK8,sK9) = sK3(sK8,sK9)
    | sP0(X0,sK8,sK9) = iProver_top
    | r1_lattice3(sK8,sK9,sK3(sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4770,c_6558])).

cnf(c_6,plain,
    ( r1_lattice3(X0,X1,sK3(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_xboole_0(X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v25_waybel_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_382,plain,
    ( r1_lattice3(X0,X1,sK3(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_xboole_0(X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v25_waybel_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_29])).

cnf(c_383,plain,
    ( r1_lattice3(sK8,X0,sK3(sK8,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | v1_xboole_0(X0)
    | v2_struct_0(sK8)
    | ~ l1_orders_2(sK8)
    | ~ v25_waybel_0(sK8) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_387,plain,
    ( r1_lattice3(sK8,X0,sK3(sK8,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | v1_xboole_0(X0)
    | ~ v25_waybel_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_383,c_30,c_27])).

cnf(c_785,plain,
    ( r1_lattice3(sK8,X0,sK3(sK8,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v25_waybel_0(sK8)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_387,c_25])).

cnf(c_786,plain,
    ( r1_lattice3(sK8,sK9,sK3(sK8,sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v25_waybel_0(sK8) ),
    inference(unflattening,[status(thm)],[c_785])).

cnf(c_788,plain,
    ( r1_lattice3(sK8,sK9,sK3(sK8,sK9))
    | ~ v25_waybel_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_786,c_24])).

cnf(c_790,plain,
    ( r1_lattice3(sK8,sK9,sK3(sK8,sK9)) = iProver_top
    | v25_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_6589,plain,
    ( sP0(X0,sK8,sK9) = iProver_top
    | sK4(X0,sK8,sK9) = sK3(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6562,c_790,c_1668,c_1678,c_6304])).

cnf(c_6590,plain,
    ( sK4(X0,sK8,sK9) = sK3(sK8,sK9)
    | sP0(X0,sK8,sK9) = iProver_top ),
    inference(renaming,[status(thm)],[c_6589])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X0)
    | r1_lattice3(X1,X2,sK6(X1,X2,X0))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_673,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X0)
    | r1_lattice3(X1,X2,sK6(X1,X2,X0))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_674,plain,
    ( ~ sP0(X0,sK8,X1)
    | ~ r1_lattice3(sK8,X1,X0)
    | r1_lattice3(sK8,X1,sK6(sK8,X1,X0))
    | r2_yellow_0(sK8,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_673])).

cnf(c_4753,plain,
    ( sP0(X0,sK8,X1) != iProver_top
    | r1_lattice3(sK8,X1,X0) != iProver_top
    | r1_lattice3(sK8,X1,sK6(sK8,X1,X0)) = iProver_top
    | r2_yellow_0(sK8,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X0)
    | ~ r1_orders_2(X1,sK6(X1,X2,X0),X0)
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_694,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X0)
    | ~ r1_orders_2(X1,sK6(X1,X2,X0),X0)
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_695,plain,
    ( ~ sP0(X0,sK8,X1)
    | ~ r1_lattice3(sK8,X1,X0)
    | ~ r1_orders_2(sK8,sK6(sK8,X1,X0),X0)
    | r2_yellow_0(sK8,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_4752,plain,
    ( sP0(X0,sK8,X1) != iProver_top
    | r1_lattice3(sK8,X1,X0) != iProver_top
    | r1_orders_2(sK8,sK6(sK8,X1,X0),X0) != iProver_top
    | r2_yellow_0(sK8,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_5551,plain,
    ( sP0(sK3(sK8,sK9),sK8,X0) != iProver_top
    | r1_lattice3(sK8,X0,sK3(sK8,sK9)) != iProver_top
    | r1_lattice3(sK8,sK9,sK6(sK8,X0,sK3(sK8,sK9))) != iProver_top
    | r2_yellow_0(sK8,X0) = iProver_top
    | m1_subset_1(sK6(sK8,X0,sK3(sK8,sK9)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK3(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | v25_waybel_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4750,c_4752])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X0)
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK6(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_652,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_lattice3(X1,X2,X0)
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK6(X1,X2,X0),u1_struct_0(X1))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_653,plain,
    ( ~ sP0(X0,sK8,X1)
    | ~ r1_lattice3(sK8,X1,X0)
    | r2_yellow_0(sK8,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X1,X0),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_652])).

cnf(c_5004,plain,
    ( ~ sP0(sK3(sK8,sK9),sK8,X0)
    | ~ r1_lattice3(sK8,X0,sK3(sK8,sK9))
    | r2_yellow_0(sK8,X0)
    | m1_subset_1(sK6(sK8,X0,sK3(sK8,sK9)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8,sK9),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_5005,plain,
    ( sP0(sK3(sK8,sK9),sK8,X0) != iProver_top
    | r1_lattice3(sK8,X0,sK3(sK8,sK9)) != iProver_top
    | r2_yellow_0(sK8,X0) = iProver_top
    | m1_subset_1(sK6(sK8,X0,sK3(sK8,sK9)),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK3(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5004])).

cnf(c_6778,plain,
    ( r2_yellow_0(sK8,X0) = iProver_top
    | r1_lattice3(sK8,sK9,sK6(sK8,X0,sK3(sK8,sK9))) != iProver_top
    | r1_lattice3(sK8,X0,sK3(sK8,sK9)) != iProver_top
    | sP0(sK3(sK8,sK9),sK8,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5551,c_752,c_1668,c_1678,c_5005,c_6304])).

cnf(c_6779,plain,
    ( sP0(sK3(sK8,sK9),sK8,X0) != iProver_top
    | r1_lattice3(sK8,X0,sK3(sK8,sK9)) != iProver_top
    | r1_lattice3(sK8,sK9,sK6(sK8,X0,sK3(sK8,sK9))) != iProver_top
    | r2_yellow_0(sK8,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6778])).

cnf(c_6788,plain,
    ( sP0(sK3(sK8,sK9),sK8,sK9) != iProver_top
    | r1_lattice3(sK8,sK9,sK3(sK8,sK9)) != iProver_top
    | r2_yellow_0(sK8,sK9) = iProver_top
    | m1_subset_1(sK3(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4753,c_6779])).

cnf(c_23,negated_conjecture,
    ( ~ r2_yellow_0(sK8,sK9)
    | ~ v25_waybel_0(sK8) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_40,plain,
    ( r2_yellow_0(sK8,sK9) != iProver_top
    | v25_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7045,plain,
    ( sP0(sK3(sK8,sK9),sK8,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6788,c_40,c_752,c_790,c_1668,c_1678,c_6304])).

cnf(c_7050,plain,
    ( sK4(sK3(sK8,sK9),sK8,sK9) = sK3(sK8,sK9) ),
    inference(superposition,[status(thm)],[c_6590,c_7045])).

cnf(c_8,plain,
    ( sP0(X0,X1,X2)
    | sK4(X0,X1,X2) != X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_5087,plain,
    ( sP0(sK3(sK8,sK9),sK8,X0)
    | sK4(sK3(sK8,sK9),sK8,X0) != sK3(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5680,plain,
    ( sP0(sK3(sK8,sK9),sK8,sK9)
    | sK4(sK3(sK8,sK9),sK8,sK9) != sK3(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_5087])).

cnf(c_5681,plain,
    ( sK4(sK3(sK8,sK9),sK8,sK9) != sK3(sK8,sK9)
    | sP0(sK3(sK8,sK9),sK8,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5680])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7050,c_6788,c_6307,c_5681,c_790,c_752,c_40])).


%------------------------------------------------------------------------------
