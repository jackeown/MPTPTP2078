%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1695+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:11 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :  230 (4218 expanded)
%              Number of clauses        :  150 ( 761 expanded)
%              Number of leaves         :   17 (1087 expanded)
%              Depth                    :   38
%              Number of atoms          : 1237 (41435 expanded)
%              Number of equality atoms :  243 ( 710 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   28 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r3_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ~ r3_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) ) )
      & ( ! [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ~ r3_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( ! [X6] :
                    ( r3_orders_2(X0,X5,X6)
                    | ~ r2_lattice3(X0,X4,X6)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r2_lattice3(X0,X4,X5)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X4,X0)
            | v1_xboole_0(X4) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r3_orders_2(X0,X5,X6)
              | ~ r2_lattice3(X0,X4,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r2_lattice3(X0,X4,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r3_orders_2(X0,sK5(X0,X4),X6)
            | ~ r2_lattice3(X0,X4,X6)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r2_lattice3(X0,X4,sK5(X0,X4))
        & m1_subset_1(sK5(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ~ r3_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_orders_2(X0,X2,sK4(X0,X2))
        & r2_lattice3(X0,X1,sK4(X0,X2))
        & m1_subset_1(sK4(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r3_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ! [X2] :
            ( ? [X3] :
                ( ~ r3_orders_2(X0,X2,X3)
                & r2_lattice3(X0,sK3(X0),X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ r2_lattice3(X0,sK3(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & v1_waybel_0(sK3(X0),X0)
        & ~ v1_xboole_0(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X2] :
              ( ( ~ r3_orders_2(X0,X2,sK4(X0,X2))
                & r2_lattice3(X0,sK3(X0),sK4(X0,X2))
                & m1_subset_1(sK4(X0,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,sK3(X0),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_0(sK3(X0),X0)
          & ~ v1_xboole_0(sK3(X0)) ) )
      & ( ! [X4] :
            ( ( ! [X6] :
                  ( r3_orders_2(X0,sK5(X0,X4),X6)
                  | ~ r2_lattice3(X0,X4,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r2_lattice3(X0,X4,sK5(X0,X4))
              & m1_subset_1(sK5(X0,X4),u1_struct_0(X0)) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X4,X0)
            | v1_xboole_0(X4) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f25,f28,f27,f26])).

fof(f56,plain,(
    ! [X2,X0] :
      ( sP0(X0)
      | r2_lattice3(X0,sK3(X0),sK4(X0,X2))
      | ~ r2_lattice3(X0,sK3(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f19,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v24_waybel_0(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v24_waybel_0(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0] :
      ( v24_waybel_0(X0)
      | ~ sP0(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v24_waybel_0(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ? [X2] :
                ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r3_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f9,f19,f18])).

fof(f58,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v24_waybel_0(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => r1_yellow_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v24_waybel_0(X0)
        <=> ! [X1] :
              ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_0(X1,X0)
                & ~ v1_xboole_0(X1) )
             => r1_yellow_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f16,plain,(
    ? [X0] :
      ( ( v24_waybel_0(X0)
      <~> ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ? [X0] :
      ( ( v24_waybel_0(X0)
      <~> ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r1_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        | ~ v24_waybel_0(X0) )
      & ( ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
        | v24_waybel_0(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f42,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r1_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        | ~ v24_waybel_0(X0) )
      & ( ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
        | v24_waybel_0(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f43,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r1_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        | ~ v24_waybel_0(X0) )
      & ( ! [X2] :
            ( r1_yellow_0(X0,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X2,X0)
            | v1_xboole_0(X2) )
        | v24_waybel_0(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f42])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ~ r1_yellow_0(X0,sK11)
        & m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_waybel_0(sK11,X0)
        & ~ v1_xboole_0(sK11) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ~ r1_yellow_0(X0,X1)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          | ~ v24_waybel_0(X0) )
        & ( ! [X2] :
              ( r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | v24_waybel_0(X0) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ? [X1] :
            ( ~ r1_yellow_0(sK10,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK10)))
            & v1_waybel_0(X1,sK10)
            & ~ v1_xboole_0(X1) )
        | ~ v24_waybel_0(sK10) )
      & ( ! [X2] :
            ( r1_yellow_0(sK10,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK10)))
            | ~ v1_waybel_0(X2,sK10)
            | v1_xboole_0(X2) )
        | v24_waybel_0(sK10) )
      & l1_orders_2(sK10)
      & v5_orders_2(sK10)
      & v3_orders_2(sK10)
      & ~ v2_struct_0(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ( ~ r1_yellow_0(sK10,sK11)
        & m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK10)))
        & v1_waybel_0(sK11,sK10)
        & ~ v1_xboole_0(sK11) )
      | ~ v24_waybel_0(sK10) )
    & ( ! [X2] :
          ( r1_yellow_0(sK10,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK10)))
          | ~ v1_waybel_0(X2,sK10)
          | v1_xboole_0(X2) )
      | v24_waybel_0(sK10) )
    & l1_orders_2(sK10)
    & v5_orders_2(sK10)
    & v3_orders_2(sK10)
    & ~ v2_struct_0(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f43,f45,f44])).

fof(f77,plain,(
    v3_orders_2(sK10) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
    l1_orders_2(sK10) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X2,X5) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ! [X3] :
          ( X2 = X3
          | ? [X4] :
              ( ~ r1_orders_2(X0,X3,X4)
              & r2_lattice3(X0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( sP2(X2,X0,X1)
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f11,f21])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ~ sP2(X2,X0,X1)
                | ? [X5] :
                    ( ~ r1_orders_2(X0,X2,X5)
                    & r2_lattice3(X0,X1,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( sP2(X2,X0,X1)
                & ! [X5] :
                    ( r1_orders_2(X0,X2,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ~ sP2(X2,X0,X1)
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( sP2(X4,X0,X1)
                & ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f35])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( sP2(X4,X0,X1)
          & ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( sP2(sK9(X0,X1),X0,X1)
        & ! [X5] :
            ( r1_orders_2(X0,sK9(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK9(X0,X1))
        & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK8(X0,X1,X2))
        & r2_lattice3(X0,X1,sK8(X0,X1,X2))
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ~ sP2(X2,X0,X1)
                | ( ~ r1_orders_2(X0,X2,sK8(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK8(X0,X1,X2))
                  & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( sP2(sK9(X0,X1),X0,X1)
              & ! [X5] :
                  ( r1_orders_2(X0,sK9(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK9(X0,X1))
              & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f36,f38,f37])).

fof(f68,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,sK9(X0,X1),X5)
      | ~ r2_lattice3(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    ! [X2,X0] :
      ( sP0(X0)
      | ~ r3_orders_2(X0,X2,sK4(X0,X2))
      | ~ r2_lattice3(X0,sK3(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ! [X2,X0] :
      ( sP0(X0)
      | m1_subset_1(sK4(X0,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,sK3(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ? [X3] :
            ( X2 != X3
            & ! [X4] :
                ( r1_orders_2(X0,X3,X4)
                | ~ r2_lattice3(X0,X1,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( X2 = X3
            | ? [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( X0 != X3
            & ! [X4] :
                ( r1_orders_2(X1,X3,X4)
                | ~ r2_lattice3(X1,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & r2_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( X0 = X5
            | ? [X6] :
                ( ~ r1_orders_2(X1,X5,X6)
                & r2_lattice3(X1,X2,X6)
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | ~ r2_lattice3(X1,X2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f30])).

fof(f33,plain,(
    ! [X5,X2,X1] :
      ( ? [X6] :
          ( ~ r1_orders_2(X1,X5,X6)
          & r2_lattice3(X1,X2,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X5,sK7(X1,X2,X5))
        & r2_lattice3(X1,X2,sK7(X1,X2,X5))
        & m1_subset_1(sK7(X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X0 != X3
          & ! [X4] :
              ( r1_orders_2(X1,X3,X4)
              | ~ r2_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( sK6(X0,X1,X2) != X0
        & ! [X4] :
            ( r1_orders_2(X1,sK6(X0,X1,X2),X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & r2_lattice3(X1,X2,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( sK6(X0,X1,X2) != X0
          & ! [X4] :
              ( r1_orders_2(X1,sK6(X0,X1,X2),X4)
              | ~ r2_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r2_lattice3(X1,X2,sK6(X0,X1,X2))
          & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( X0 = X5
            | ( ~ r1_orders_2(X1,X5,sK7(X1,X2,X5))
              & r2_lattice3(X1,X2,sK7(X1,X2,X5))
              & m1_subset_1(sK7(X1,X2,X5),u1_struct_0(X1)) )
            | ~ r2_lattice3(X1,X2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f31,f33,f32])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | r2_lattice3(X1,X2,sK6(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | r1_orders_2(X1,sK6(X0,X1,X2),X4)
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f82,plain,
    ( v1_waybel_0(sK11,sK10)
    | ~ v24_waybel_0(sK10) ),
    inference(cnf_transformation,[],[f46])).

fof(f51,plain,(
    ! [X6,X4,X0] :
      ( r3_orders_2(X0,sK5(X0,X4),X6)
      | ~ r2_lattice3(X0,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X4,X0)
      | v1_xboole_0(X4)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f49,plain,(
    ! [X4,X0] :
      ( m1_subset_1(sK5(X0,X4),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X4,X0)
      | v1_xboole_0(X4)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,
    ( ~ v1_xboole_0(sK11)
    | ~ v24_waybel_0(sK10) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK10)))
    | ~ v24_waybel_0(sK10) ),
    inference(cnf_transformation,[],[f46])).

fof(f47,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v24_waybel_0(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    v5_orders_2(sK10) ),
    inference(cnf_transformation,[],[f46])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    ! [X4,X0] :
      ( r2_lattice3(X0,X4,sK5(X0,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X4,X0)
      | v1_xboole_0(X4)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ sP2(X2,X0,X1)
      | r2_lattice3(X0,X1,sK8(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ sP2(X2,X0,X1)
      | ~ r1_orders_2(X0,X2,sK8(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ sP2(X2,X0,X1)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,
    ( ~ r1_yellow_0(sK10,sK11)
    | ~ v24_waybel_0(sK10) ),
    inference(cnf_transformation,[],[f46])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | sK6(X0,X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f53,plain,(
    ! [X0] :
      ( sP0(X0)
      | v1_waybel_0(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    ! [X2] :
      ( r1_yellow_0(sK10,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK10)))
      | ~ v1_waybel_0(X2,sK10)
      | v1_xboole_0(X2)
      | v24_waybel_0(sK10) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f52,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_xboole_0(sK3(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK9(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3,plain,
    ( ~ r2_lattice3(X0,sK3(X0),X1)
    | r2_lattice3(X0,sK3(X0),sK4(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_0,plain,
    ( ~ sP1(X0)
    | ~ sP0(X0)
    | v24_waybel_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sP1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_36,negated_conjecture,
    ( v3_orders_2(sK10) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_561,plain,
    ( v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sP1(X0)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_36])).

cnf(c_562,plain,
    ( v2_struct_0(sK10)
    | ~ l1_orders_2(sK10)
    | sP1(sK10) ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,negated_conjecture,
    ( l1_orders_2(sK10) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_101,plain,
    ( v2_struct_0(sK10)
    | ~ v3_orders_2(sK10)
    | ~ l1_orders_2(sK10)
    | sP1(sK10) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_564,plain,
    ( sP1(sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_562,c_37,c_36,c_34,c_101])).

cnf(c_594,plain,
    ( ~ sP0(X0)
    | v24_waybel_0(X0)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_564])).

cnf(c_595,plain,
    ( ~ sP0(sK10)
    | v24_waybel_0(sK10) ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_1134,plain,
    ( ~ r2_lattice3(X0,sK3(X0),X1)
    | r2_lattice3(X0,sK3(X0),sK4(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v24_waybel_0(sK10)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_595])).

cnf(c_1135,plain,
    ( ~ r2_lattice3(sK10,sK3(sK10),X0)
    | r2_lattice3(sK10,sK3(sK10),sK4(sK10,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | v24_waybel_0(sK10) ),
    inference(unflattening,[status(thm)],[c_1134])).

cnf(c_5095,plain,
    ( r2_lattice3(sK10,sK3(sK10),X0) != iProver_top
    | r2_lattice3(sK10,sK3(sK10),sK4(sK10,X0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | v24_waybel_0(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1135])).

cnf(c_23,plain,
    ( r1_orders_2(X0,sK9(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_634,plain,
    ( r1_orders_2(X0,sK9(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_635,plain,
    ( r1_orders_2(sK10,sK9(sK10,X0),X1)
    | ~ r2_lattice3(sK10,X0,X1)
    | ~ r1_yellow_0(sK10,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK10)) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_5107,plain,
    ( r1_orders_2(sK10,sK9(sK10,X0),X1) = iProver_top
    | r2_lattice3(sK10,X0,X1) != iProver_top
    | r1_yellow_0(sK10,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_2,plain,
    ( ~ r2_lattice3(X0,sK3(X0),X1)
    | ~ r3_orders_2(X0,X1,sK4(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_26,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_537,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_36])).

cnf(c_538,plain,
    ( ~ r1_orders_2(sK10,X0,X1)
    | r3_orders_2(sK10,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | v2_struct_0(sK10)
    | ~ l1_orders_2(sK10) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_542,plain,
    ( ~ r1_orders_2(sK10,X0,X1)
    | r3_orders_2(sK10,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | ~ m1_subset_1(X0,u1_struct_0(sK10)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_37,c_34])).

cnf(c_762,plain,
    ( ~ r1_orders_2(sK10,X0,X1)
    | ~ r2_lattice3(X2,sK3(X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | sP0(X2)
    | X0 != X3
    | sK4(X2,X3) != X1
    | sK10 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_542])).

cnf(c_763,plain,
    ( ~ r1_orders_2(sK10,X0,sK4(sK10,X0))
    | ~ r2_lattice3(sK10,sK3(sK10),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ m1_subset_1(sK4(sK10,X0),u1_struct_0(sK10))
    | sP0(sK10) ),
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_4,plain,
    ( ~ r2_lattice3(X0,sK3(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_777,plain,
    ( ~ r1_orders_2(sK10,X0,sK4(sK10,X0))
    | ~ r2_lattice3(sK10,sK3(sK10),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | sP0(sK10) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_763,c_4])).

cnf(c_1088,plain,
    ( ~ r1_orders_2(sK10,X0,sK4(sK10,X0))
    | ~ r2_lattice3(sK10,sK3(sK10),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | v24_waybel_0(sK10) ),
    inference(resolution,[status(thm)],[c_777,c_595])).

cnf(c_5098,plain,
    ( r1_orders_2(sK10,X0,sK4(sK10,X0)) != iProver_top
    | r2_lattice3(sK10,sK3(sK10),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | v24_waybel_0(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1088])).

cnf(c_38,plain,
    ( v2_struct_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_39,plain,
    ( v3_orders_2(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_41,plain,
    ( l1_orders_2(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_100,plain,
    ( v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | sP1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_102,plain,
    ( v2_struct_0(sK10) = iProver_top
    | v3_orders_2(sK10) != iProver_top
    | l1_orders_2(sK10) != iProver_top
    | sP1(sK10) = iProver_top ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_133,plain,
    ( sP1(X0) != iProver_top
    | sP0(X0) != iProver_top
    | v24_waybel_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_135,plain,
    ( sP1(sK10) != iProver_top
    | sP0(sK10) != iProver_top
    | v24_waybel_0(sK10) = iProver_top ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_764,plain,
    ( r1_orders_2(sK10,X0,sK4(sK10,X0)) != iProver_top
    | r2_lattice3(sK10,sK3(sK10),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(sK4(sK10,X0),u1_struct_0(sK10)) != iProver_top
    | sP0(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_1116,plain,
    ( ~ r2_lattice3(X0,sK3(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | v24_waybel_0(sK10)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_595])).

cnf(c_1117,plain,
    ( ~ r2_lattice3(sK10,sK3(sK10),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | m1_subset_1(sK4(sK10,X0),u1_struct_0(sK10))
    | v24_waybel_0(sK10) ),
    inference(unflattening,[status(thm)],[c_1116])).

cnf(c_1118,plain,
    ( r2_lattice3(sK10,sK3(sK10),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(sK4(sK10,X0),u1_struct_0(sK10)) = iProver_top
    | v24_waybel_0(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1117])).

cnf(c_14,plain,
    ( sP2(X0,X1,X2)
    | r2_lattice3(X1,X2,sK6(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_5117,plain,
    ( sP2(X0,X1,X2) = iProver_top
    | r2_lattice3(X1,X2,sK6(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( r1_orders_2(X0,sK6(X1,X0,X2),X3)
    | sP2(X1,X0,X2)
    | ~ r2_lattice3(X0,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_5118,plain,
    ( r1_orders_2(X0,sK6(X1,X0,X2),X3) = iProver_top
    | sP2(X1,X0,X2) = iProver_top
    | r2_lattice3(X0,X2,X3) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_31,negated_conjecture,
    ( v1_waybel_0(sK11,sK10)
    | ~ v24_waybel_0(sK10) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_8,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r3_orders_2(X0,sK5(X0,X1),X2)
    | ~ v1_waybel_0(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v1_xboole_0(X1)
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_27,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_513,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_36])).

cnf(c_514,plain,
    ( r1_orders_2(sK10,X0,X1)
    | ~ r3_orders_2(sK10,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | v2_struct_0(sK10)
    | ~ l1_orders_2(sK10) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_518,plain,
    ( r1_orders_2(sK10,X0,X1)
    | ~ r3_orders_2(sK10,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | ~ m1_subset_1(X0,u1_struct_0(sK10)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_37,c_34])).

cnf(c_785,plain,
    ( r1_orders_2(sK10,X0,X1)
    | ~ r2_lattice3(X2,X3,X4)
    | ~ v1_waybel_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | v1_xboole_0(X3)
    | ~ sP0(X2)
    | X1 != X4
    | sK5(X2,X3) != X0
    | sK10 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_518])).

cnf(c_786,plain,
    ( r1_orders_2(sK10,sK5(sK10,X0),X1)
    | ~ r2_lattice3(sK10,X0,X1)
    | ~ v1_waybel_0(X0,sK10)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK10)))
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | ~ m1_subset_1(sK5(sK10,X0),u1_struct_0(sK10))
    | v1_xboole_0(X0)
    | ~ sP0(sK10) ),
    inference(unflattening,[status(thm)],[c_785])).

cnf(c_10,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
    | v1_xboole_0(X0)
    | ~ sP0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_806,plain,
    ( r1_orders_2(sK10,sK5(sK10,X0),X1)
    | ~ r2_lattice3(sK10,X0,X1)
    | ~ v1_waybel_0(X0,sK10)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK10)))
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | v1_xboole_0(X0)
    | ~ sP0(sK10) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_786,c_10])).

cnf(c_1048,plain,
    ( r1_orders_2(sK10,sK5(sK10,X0),X1)
    | ~ r2_lattice3(sK10,X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK10)))
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | v1_xboole_0(X0)
    | ~ sP0(sK10)
    | ~ v24_waybel_0(sK10)
    | sK11 != X0
    | sK10 != sK10 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_806])).

cnf(c_1049,plain,
    ( r1_orders_2(sK10,sK5(sK10,sK11),X0)
    | ~ r2_lattice3(sK10,sK11,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK10)))
    | v1_xboole_0(sK11)
    | ~ sP0(sK10)
    | ~ v24_waybel_0(sK10) ),
    inference(unflattening,[status(thm)],[c_1048])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK11)
    | ~ v24_waybel_0(sK10) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK10)))
    | ~ v24_waybel_0(sK10) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1,plain,
    ( ~ sP1(X0)
    | sP0(X0)
    | ~ v24_waybel_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_131,plain,
    ( ~ sP1(sK10)
    | sP0(sK10)
    | ~ v24_waybel_0(sK10) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1053,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ r2_lattice3(sK10,sK11,X0)
    | r1_orders_2(sK10,sK5(sK10,sK11),X0)
    | ~ v24_waybel_0(sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1049,c_37,c_36,c_34,c_32,c_30,c_101,c_131])).

cnf(c_1054,plain,
    ( r1_orders_2(sK10,sK5(sK10,sK11),X0)
    | ~ r2_lattice3(sK10,sK11,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ v24_waybel_0(sK10) ),
    inference(renaming,[status(thm)],[c_1053])).

cnf(c_5099,plain,
    ( r1_orders_2(sK10,sK5(sK10,sK11),X0) = iProver_top
    | r2_lattice3(sK10,sK11,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | v24_waybel_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1054])).

cnf(c_28,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | X1 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,negated_conjecture,
    ( v5_orders_2(sK10) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_430,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X2 = X1
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_35])).

cnf(c_431,plain,
    ( ~ r1_orders_2(sK10,X0,X1)
    | ~ r1_orders_2(sK10,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | ~ l1_orders_2(sK10)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK10))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | ~ r1_orders_2(sK10,X1,X0)
    | ~ r1_orders_2(sK10,X0,X1)
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_431,c_34])).

cnf(c_436,plain,
    ( ~ r1_orders_2(sK10,X0,X1)
    | ~ r1_orders_2(sK10,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK10))
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_435])).

cnf(c_5110,plain,
    ( X0 = X1
    | r1_orders_2(sK10,X0,X1) != iProver_top
    | r1_orders_2(sK10,X1,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_5798,plain,
    ( sK5(sK10,sK11) = X0
    | r1_orders_2(sK10,X0,sK5(sK10,sK11)) != iProver_top
    | r2_lattice3(sK10,sK11,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(sK5(sK10,sK11),u1_struct_0(sK10)) != iProver_top
    | v24_waybel_0(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_5099,c_5110])).

cnf(c_1034,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
    | v1_xboole_0(X0)
    | ~ sP0(X1)
    | ~ v24_waybel_0(sK10)
    | sK11 != X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_31])).

cnf(c_1035,plain,
    ( m1_subset_1(sK5(sK10,sK11),u1_struct_0(sK10))
    | ~ m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK10)))
    | v1_xboole_0(sK11)
    | ~ sP0(sK10)
    | ~ v24_waybel_0(sK10) ),
    inference(unflattening,[status(thm)],[c_1034])).

cnf(c_1037,plain,
    ( m1_subset_1(sK5(sK10,sK11),u1_struct_0(sK10))
    | ~ v24_waybel_0(sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1035,c_37,c_36,c_34,c_32,c_30,c_101,c_131])).

cnf(c_1039,plain,
    ( m1_subset_1(sK5(sK10,sK11),u1_struct_0(sK10)) = iProver_top
    | v24_waybel_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1037])).

cnf(c_6036,plain,
    ( m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | r2_lattice3(sK10,sK11,X0) != iProver_top
    | r1_orders_2(sK10,X0,sK5(sK10,sK11)) != iProver_top
    | sK5(sK10,sK11) = X0
    | v24_waybel_0(sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5798,c_1039])).

cnf(c_6037,plain,
    ( sK5(sK10,sK11) = X0
    | r1_orders_2(sK10,X0,sK5(sK10,sK11)) != iProver_top
    | r2_lattice3(sK10,sK11,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | v24_waybel_0(sK10) != iProver_top ),
    inference(renaming,[status(thm)],[c_6036])).

cnf(c_6047,plain,
    ( sK6(X0,sK10,X1) = sK5(sK10,sK11)
    | sP2(X0,sK10,X1) = iProver_top
    | r2_lattice3(sK10,X1,sK5(sK10,sK11)) != iProver_top
    | r2_lattice3(sK10,sK11,sK6(X0,sK10,X1)) != iProver_top
    | m1_subset_1(sK6(X0,sK10,X1),u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(sK5(sK10,sK11),u1_struct_0(sK10)) != iProver_top
    | v24_waybel_0(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_5118,c_6037])).

cnf(c_6915,plain,
    ( m1_subset_1(sK6(X0,sK10,X1),u1_struct_0(sK10)) != iProver_top
    | r2_lattice3(sK10,sK11,sK6(X0,sK10,X1)) != iProver_top
    | r2_lattice3(sK10,X1,sK5(sK10,sK11)) != iProver_top
    | sP2(X0,sK10,X1) = iProver_top
    | sK6(X0,sK10,X1) = sK5(sK10,sK11)
    | v24_waybel_0(sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6047,c_1039])).

cnf(c_6916,plain,
    ( sK6(X0,sK10,X1) = sK5(sK10,sK11)
    | sP2(X0,sK10,X1) = iProver_top
    | r2_lattice3(sK10,X1,sK5(sK10,sK11)) != iProver_top
    | r2_lattice3(sK10,sK11,sK6(X0,sK10,X1)) != iProver_top
    | m1_subset_1(sK6(X0,sK10,X1),u1_struct_0(sK10)) != iProver_top
    | v24_waybel_0(sK10) != iProver_top ),
    inference(renaming,[status(thm)],[c_6915])).

cnf(c_15,plain,
    ( sP2(X0,X1,X2)
    | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_5116,plain,
    ( sP2(X0,X1,X2) = iProver_top
    | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6927,plain,
    ( sK6(X0,sK10,X1) = sK5(sK10,sK11)
    | sP2(X0,sK10,X1) = iProver_top
    | r2_lattice3(sK10,X1,sK5(sK10,sK11)) != iProver_top
    | r2_lattice3(sK10,sK11,sK6(X0,sK10,X1)) != iProver_top
    | v24_waybel_0(sK10) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6916,c_5116])).

cnf(c_6931,plain,
    ( sK6(X0,sK10,sK11) = sK5(sK10,sK11)
    | sP2(X0,sK10,sK11) = iProver_top
    | r2_lattice3(sK10,sK11,sK5(sK10,sK11)) != iProver_top
    | v24_waybel_0(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_6927])).

cnf(c_9,plain,
    ( r2_lattice3(X0,X1,sK5(X0,X1))
    | ~ v1_waybel_0(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_xboole_0(X1)
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1020,plain,
    ( r2_lattice3(X0,X1,sK5(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_xboole_0(X1)
    | ~ sP0(X0)
    | ~ v24_waybel_0(sK10)
    | sK11 != X1
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_31])).

cnf(c_1021,plain,
    ( r2_lattice3(sK10,sK11,sK5(sK10,sK11))
    | ~ m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK10)))
    | v1_xboole_0(sK11)
    | ~ sP0(sK10)
    | ~ v24_waybel_0(sK10) ),
    inference(unflattening,[status(thm)],[c_1020])).

cnf(c_1023,plain,
    ( r2_lattice3(sK10,sK11,sK5(sK10,sK11))
    | ~ v24_waybel_0(sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1021,c_37,c_36,c_34,c_32,c_30,c_101,c_131])).

cnf(c_1025,plain,
    ( r2_lattice3(sK10,sK11,sK5(sK10,sK11)) = iProver_top
    | v24_waybel_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1023])).

cnf(c_6936,plain,
    ( sP2(X0,sK10,sK11) = iProver_top
    | sK6(X0,sK10,sK11) = sK5(sK10,sK11)
    | v24_waybel_0(sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6931,c_1025])).

cnf(c_6937,plain,
    ( sK6(X0,sK10,sK11) = sK5(sK10,sK11)
    | sP2(X0,sK10,sK11) = iProver_top
    | v24_waybel_0(sK10) != iProver_top ),
    inference(renaming,[status(thm)],[c_6936])).

cnf(c_20,plain,
    ( ~ sP2(X0,X1,X2)
    | ~ r2_lattice3(X1,X2,X0)
    | r2_lattice3(X1,X2,sK8(X1,X2,X0))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_706,plain,
    ( ~ sP2(X0,X1,X2)
    | ~ r2_lattice3(X1,X2,X0)
    | r2_lattice3(X1,X2,sK8(X1,X2,X0))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_34])).

cnf(c_707,plain,
    ( ~ sP2(X0,sK10,X1)
    | ~ r2_lattice3(sK10,X1,X0)
    | r2_lattice3(sK10,X1,sK8(sK10,X1,X0))
    | r1_yellow_0(sK10,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK10)) ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_5103,plain,
    ( sP2(X0,sK10,X1) != iProver_top
    | r2_lattice3(sK10,X1,X0) != iProver_top
    | r2_lattice3(sK10,X1,sK8(sK10,X1,X0)) = iProver_top
    | r1_yellow_0(sK10,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_707])).

cnf(c_19,plain,
    ( ~ r1_orders_2(X0,X1,sK8(X0,X2,X1))
    | ~ sP2(X1,X0,X2)
    | ~ r2_lattice3(X0,X2,X1)
    | r1_yellow_0(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_664,plain,
    ( ~ r1_orders_2(X0,X1,sK8(X0,X2,X1))
    | ~ sP2(X1,X0,X2)
    | ~ r2_lattice3(X0,X2,X1)
    | r1_yellow_0(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_34])).

cnf(c_665,plain,
    ( ~ r1_orders_2(sK10,X0,sK8(sK10,X1,X0))
    | ~ sP2(X0,sK10,X1)
    | ~ r2_lattice3(sK10,X1,X0)
    | r1_yellow_0(sK10,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK10)) ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_5105,plain,
    ( r1_orders_2(sK10,X0,sK8(sK10,X1,X0)) != iProver_top
    | sP2(X0,sK10,X1) != iProver_top
    | r2_lattice3(sK10,X1,X0) != iProver_top
    | r1_yellow_0(sK10,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_5852,plain,
    ( sP2(sK5(sK10,sK11),sK10,X0) != iProver_top
    | r2_lattice3(sK10,X0,sK5(sK10,sK11)) != iProver_top
    | r2_lattice3(sK10,sK11,sK8(sK10,X0,sK5(sK10,sK11))) != iProver_top
    | r1_yellow_0(sK10,X0) = iProver_top
    | m1_subset_1(sK8(sK10,X0,sK5(sK10,sK11)),u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(sK5(sK10,sK11),u1_struct_0(sK10)) != iProver_top
    | v24_waybel_0(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_5099,c_5105])).

cnf(c_21,plain,
    ( ~ sP2(X0,X1,X2)
    | ~ r2_lattice3(X1,X2,X0)
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK8(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_685,plain,
    ( ~ sP2(X0,X1,X2)
    | ~ r2_lattice3(X1,X2,X0)
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK8(X1,X2,X0),u1_struct_0(X1))
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_34])).

cnf(c_686,plain,
    ( ~ sP2(X0,sK10,X1)
    | ~ r2_lattice3(sK10,X1,X0)
    | r1_yellow_0(sK10,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK10))
    | m1_subset_1(sK8(sK10,X1,X0),u1_struct_0(sK10)) ),
    inference(unflattening,[status(thm)],[c_685])).

cnf(c_5351,plain,
    ( ~ sP2(sK5(sK10,sK11),sK10,X0)
    | ~ r2_lattice3(sK10,X0,sK5(sK10,sK11))
    | r1_yellow_0(sK10,X0)
    | m1_subset_1(sK8(sK10,X0,sK5(sK10,sK11)),u1_struct_0(sK10))
    | ~ m1_subset_1(sK5(sK10,sK11),u1_struct_0(sK10)) ),
    inference(instantiation,[status(thm)],[c_686])).

cnf(c_5352,plain,
    ( sP2(sK5(sK10,sK11),sK10,X0) != iProver_top
    | r2_lattice3(sK10,X0,sK5(sK10,sK11)) != iProver_top
    | r1_yellow_0(sK10,X0) = iProver_top
    | m1_subset_1(sK8(sK10,X0,sK5(sK10,sK11)),u1_struct_0(sK10)) = iProver_top
    | m1_subset_1(sK5(sK10,sK11),u1_struct_0(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5351])).

cnf(c_6646,plain,
    ( sP2(sK5(sK10,sK11),sK10,X0) != iProver_top
    | r2_lattice3(sK10,X0,sK5(sK10,sK11)) != iProver_top
    | r2_lattice3(sK10,sK11,sK8(sK10,X0,sK5(sK10,sK11))) != iProver_top
    | r1_yellow_0(sK10,X0) = iProver_top
    | v24_waybel_0(sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5852,c_1039,c_5352])).

cnf(c_6657,plain,
    ( sP2(sK5(sK10,sK11),sK10,sK11) != iProver_top
    | r2_lattice3(sK10,sK11,sK5(sK10,sK11)) != iProver_top
    | r1_yellow_0(sK10,sK11) = iProver_top
    | m1_subset_1(sK5(sK10,sK11),u1_struct_0(sK10)) != iProver_top
    | v24_waybel_0(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_5103,c_6646])).

cnf(c_29,negated_conjecture,
    ( ~ r1_yellow_0(sK10,sK11)
    | ~ v24_waybel_0(sK10) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_48,plain,
    ( r1_yellow_0(sK10,sK11) != iProver_top
    | v24_waybel_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6660,plain,
    ( sP2(sK5(sK10,sK11),sK10,sK11) != iProver_top
    | v24_waybel_0(sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6657,c_48,c_1025,c_1039])).

cnf(c_6947,plain,
    ( sK6(sK5(sK10,sK11),sK10,sK11) = sK5(sK10,sK11)
    | v24_waybel_0(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_6937,c_6660])).

cnf(c_12,plain,
    ( sP2(X0,X1,X2)
    | sK6(X0,X1,X2) != X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_5434,plain,
    ( sP2(sK5(sK10,sK11),sK10,X0)
    | sK6(sK5(sK10,sK11),sK10,X0) != sK5(sK10,sK11) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_5997,plain,
    ( sP2(sK5(sK10,sK11),sK10,sK11)
    | sK6(sK5(sK10,sK11),sK10,sK11) != sK5(sK10,sK11) ),
    inference(instantiation,[status(thm)],[c_5434])).

cnf(c_5998,plain,
    ( sK6(sK5(sK10,sK11),sK10,sK11) != sK5(sK10,sK11)
    | sP2(sK5(sK10,sK11),sK10,sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5997])).

cnf(c_7294,plain,
    ( v24_waybel_0(sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6947,c_5998,c_6660])).

cnf(c_7300,plain,
    ( m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top
    | r2_lattice3(sK10,sK3(sK10),X0) != iProver_top
    | r1_orders_2(sK10,X0,sK4(sK10,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5098,c_38,c_39,c_41,c_102,c_135,c_764,c_1118,c_5998,c_6660,c_6947])).

cnf(c_7301,plain,
    ( r1_orders_2(sK10,X0,sK4(sK10,X0)) != iProver_top
    | r2_lattice3(sK10,sK3(sK10),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK10)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7300])).

cnf(c_7310,plain,
    ( r2_lattice3(sK10,X0,sK4(sK10,sK9(sK10,X0))) != iProver_top
    | r2_lattice3(sK10,sK3(sK10),sK9(sK10,X0)) != iProver_top
    | r1_yellow_0(sK10,X0) != iProver_top
    | m1_subset_1(sK9(sK10,X0),u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(sK4(sK10,sK9(sK10,X0)),u1_struct_0(sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5107,c_7301])).

cnf(c_25,plain,
    ( ~ r1_yellow_0(X0,X1)
    | m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_610,plain,
    ( ~ r1_yellow_0(X0,X1)
    | m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_611,plain,
    ( ~ r1_yellow_0(sK10,X0)
    | m1_subset_1(sK9(sK10,X0),u1_struct_0(sK10)) ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_612,plain,
    ( r1_yellow_0(sK10,X0) != iProver_top
    | m1_subset_1(sK9(sK10,X0),u1_struct_0(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_7432,plain,
    ( r1_yellow_0(sK10,X0) != iProver_top
    | r2_lattice3(sK10,sK3(sK10),sK9(sK10,X0)) != iProver_top
    | r2_lattice3(sK10,X0,sK4(sK10,sK9(sK10,X0))) != iProver_top
    | m1_subset_1(sK4(sK10,sK9(sK10,X0)),u1_struct_0(sK10)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7310,c_612])).

cnf(c_7433,plain,
    ( r2_lattice3(sK10,X0,sK4(sK10,sK9(sK10,X0))) != iProver_top
    | r2_lattice3(sK10,sK3(sK10),sK9(sK10,X0)) != iProver_top
    | r1_yellow_0(sK10,X0) != iProver_top
    | m1_subset_1(sK4(sK10,sK9(sK10,X0)),u1_struct_0(sK10)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7432])).

cnf(c_7442,plain,
    ( r2_lattice3(sK10,sK3(sK10),sK9(sK10,sK3(sK10))) != iProver_top
    | r1_yellow_0(sK10,sK3(sK10)) != iProver_top
    | m1_subset_1(sK9(sK10,sK3(sK10)),u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(sK4(sK10,sK9(sK10,sK3(sK10))),u1_struct_0(sK10)) != iProver_top
    | v24_waybel_0(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_5095,c_7433])).

cnf(c_7204,plain,
    ( ~ r2_lattice3(sK10,sK3(sK10),sK9(sK10,sK3(sK10)))
    | ~ m1_subset_1(sK9(sK10,sK3(sK10)),u1_struct_0(sK10))
    | m1_subset_1(sK4(sK10,sK9(sK10,sK3(sK10))),u1_struct_0(sK10))
    | v24_waybel_0(sK10) ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_7226,plain,
    ( r2_lattice3(sK10,sK3(sK10),sK9(sK10,sK3(sK10))) != iProver_top
    | m1_subset_1(sK9(sK10,sK3(sK10)),u1_struct_0(sK10)) != iProver_top
    | m1_subset_1(sK4(sK10,sK9(sK10,sK3(sK10))),u1_struct_0(sK10)) = iProver_top
    | v24_waybel_0(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7204])).

cnf(c_6,plain,
    ( v1_waybel_0(sK3(X0),X0)
    | sP0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_33,negated_conjecture,
    ( r1_yellow_0(sK10,X0)
    | ~ v1_waybel_0(X0,sK10)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK10)))
    | v1_xboole_0(X0)
    | v24_waybel_0(sK10) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1006,plain,
    ( r1_yellow_0(sK10,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK10)))
    | v1_xboole_0(X0)
    | sP0(X1)
    | v24_waybel_0(sK10)
    | sK3(X1) != X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_33])).

cnf(c_1007,plain,
    ( r1_yellow_0(sK10,sK3(sK10))
    | ~ m1_subset_1(sK3(sK10),k1_zfmisc_1(u1_struct_0(sK10)))
    | v1_xboole_0(sK3(sK10))
    | sP0(sK10)
    | v24_waybel_0(sK10) ),
    inference(unflattening,[status(thm)],[c_1006])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(sK3(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_113,plain,
    ( ~ v1_xboole_0(sK3(sK10))
    | sP0(sK10) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_119,plain,
    ( m1_subset_1(sK3(sK10),k1_zfmisc_1(u1_struct_0(sK10)))
    | sP0(sK10) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_134,plain,
    ( ~ sP1(sK10)
    | ~ sP0(sK10)
    | v24_waybel_0(sK10) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1009,plain,
    ( r1_yellow_0(sK10,sK3(sK10))
    | v24_waybel_0(sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1007,c_37,c_36,c_34,c_101,c_113,c_119,c_134])).

cnf(c_2011,plain,
    ( m1_subset_1(sK9(sK10,X0),u1_struct_0(sK10))
    | v24_waybel_0(sK10)
    | sK3(sK10) != X0
    | sK10 != sK10 ),
    inference(resolution_lifted,[status(thm)],[c_611,c_1009])).

cnf(c_2012,plain,
    ( m1_subset_1(sK9(sK10,sK3(sK10)),u1_struct_0(sK10))
    | v24_waybel_0(sK10) ),
    inference(unflattening,[status(thm)],[c_2011])).

cnf(c_2013,plain,
    ( m1_subset_1(sK9(sK10,sK3(sK10)),u1_struct_0(sK10)) = iProver_top
    | v24_waybel_0(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2012])).

cnf(c_24,plain,
    ( r2_lattice3(X0,X1,sK9(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_622,plain,
    ( r2_lattice3(X0,X1,sK9(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_34])).

cnf(c_623,plain,
    ( r2_lattice3(sK10,X0,sK9(sK10,X0))
    | ~ r1_yellow_0(sK10,X0) ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_2001,plain,
    ( r2_lattice3(sK10,X0,sK9(sK10,X0))
    | v24_waybel_0(sK10)
    | sK3(sK10) != X0
    | sK10 != sK10 ),
    inference(resolution_lifted,[status(thm)],[c_623,c_1009])).

cnf(c_2002,plain,
    ( r2_lattice3(sK10,sK3(sK10),sK9(sK10,sK3(sK10)))
    | v24_waybel_0(sK10) ),
    inference(unflattening,[status(thm)],[c_2001])).

cnf(c_2003,plain,
    ( r2_lattice3(sK10,sK3(sK10),sK9(sK10,sK3(sK10))) = iProver_top
    | v24_waybel_0(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2002])).

cnf(c_1011,plain,
    ( r1_yellow_0(sK10,sK3(sK10)) = iProver_top
    | v24_waybel_0(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1009])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7442,c_7294,c_7226,c_2013,c_2003,c_1011])).


%------------------------------------------------------------------------------
