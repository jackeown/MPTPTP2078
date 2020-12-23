%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1660+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:17 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  143 (1887 expanded)
%              Number of leaves         :   19 ( 657 expanded)
%              Depth                    :   44
%              Number of atoms          : 1084 (22831 expanded)
%              Number of equality atoms :   18 ( 208 expanded)
%              Maximal formula depth    :   17 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f548,plain,(
    $false ),
    inference(subsumption_resolution,[],[f546,f202])).

fof(f202,plain,(
    v1_waybel_0(sK3,sK2) ),
    inference(resolution,[],[f201,f102])).

fof(f102,plain,
    ( ~ sP0(sK2,sK3)
    | v1_waybel_0(sK3,sK2) ),
    inference(resolution,[],[f100,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v1_waybel_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v1_waybel_0(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v1_waybel_0(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ( ( v1_waybel_0(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v1_waybel_0(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ( v1_waybel_0(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f100,plain,(
    sP1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f99,f57])).

fof(f57,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ( ~ r2_hidden(k13_lattice3(sK2,sK4,sK5),sK3)
        & r2_hidden(sK5,sK3)
        & r2_hidden(sK4,sK3)
        & m1_subset_1(sK5,u1_struct_0(sK2))
        & m1_subset_1(sK4,u1_struct_0(sK2)) )
      | ~ v1_waybel_0(sK3,sK2) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r2_hidden(k13_lattice3(sK2,X4,X5),sK3)
              | ~ r2_hidden(X5,sK3)
              | ~ r2_hidden(X4,sK3)
              | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
          | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
      | v1_waybel_0(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v12_waybel_0(sK3,sK2)
    & l1_orders_2(sK2)
    & v1_lattice3(sK2)
    & v5_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f31,f35,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v1_waybel_0(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | v1_waybel_0(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k13_lattice3(sK2,X2,X3),X1)
                    & r2_hidden(X3,X1)
                    & r2_hidden(X2,X1)
                    & m1_subset_1(X3,u1_struct_0(sK2)) )
                & m1_subset_1(X2,u1_struct_0(sK2)) )
            | ~ v1_waybel_0(X1,sK2) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k13_lattice3(sK2,X4,X5),X1)
                    | ~ r2_hidden(X5,X1)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
                | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
            | v1_waybel_0(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & v12_waybel_0(X1,sK2) )
      & l1_orders_2(sK2)
      & v1_lattice3(sK2)
      & v5_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k13_lattice3(sK2,X2,X3),X1)
                  & r2_hidden(X3,X1)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X3,u1_struct_0(sK2)) )
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          | ~ v1_waybel_0(X1,sK2) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(k13_lattice3(sK2,X4,X5),X1)
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
              | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
          | v1_waybel_0(X1,sK2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & v12_waybel_0(X1,sK2) )
   => ( ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k13_lattice3(sK2,X2,X3),sK3)
                & r2_hidden(X3,sK3)
                & r2_hidden(X2,sK3)
                & m1_subset_1(X3,u1_struct_0(sK2)) )
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        | ~ v1_waybel_0(sK3,sK2) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(k13_lattice3(sK2,X4,X5),sK3)
                | ~ r2_hidden(X5,sK3)
                | ~ r2_hidden(X4,sK3)
                | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
            | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
        | v1_waybel_0(sK3,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & v12_waybel_0(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_hidden(k13_lattice3(sK2,X2,X3),sK3)
            & r2_hidden(X3,sK3)
            & r2_hidden(X2,sK3)
            & m1_subset_1(X3,u1_struct_0(sK2)) )
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( ? [X3] :
          ( ~ r2_hidden(k13_lattice3(sK2,sK4,X3),sK3)
          & r2_hidden(X3,sK3)
          & r2_hidden(sK4,sK3)
          & m1_subset_1(X3,u1_struct_0(sK2)) )
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X3] :
        ( ~ r2_hidden(k13_lattice3(sK2,sK4,X3),sK3)
        & r2_hidden(X3,sK3)
        & r2_hidden(sK4,sK3)
        & m1_subset_1(X3,u1_struct_0(sK2)) )
   => ( ~ r2_hidden(k13_lattice3(sK2,sK4,sK5),sK3)
      & r2_hidden(sK5,sK3)
      & r2_hidden(sK4,sK3)
      & m1_subset_1(sK5,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    & r2_hidden(X3,X1)
                    & r2_hidden(X2,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v1_waybel_0(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k13_lattice3(X0,X4,X5),X1)
                    | ~ r2_hidden(X5,X1)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    & r2_hidden(X3,X1)
                    & r2_hidden(X2,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v1_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    & r2_hidden(X3,X1)
                    & r2_hidden(X2,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v1_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0) )
           => ( v1_waybel_0(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( ( r2_hidden(X3,X1)
                          & r2_hidden(X2,X1) )
                       => r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_waybel_0)).

fof(f99,plain,
    ( sP1(sK3,sK2)
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f77,f59])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f13,f27,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( r1_orders_2(X0,X3,X4)
                  & r1_orders_2(X0,X2,X4)
                  & r2_hidden(X4,X1)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X3,X4)
                                & r1_orders_2(X0,X2,X4)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_waybel_0)).

fof(f201,plain,(
    sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f200,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X4] :
              ( ~ r1_orders_2(X0,sK7(X0,X1),X4)
              | ~ r1_orders_2(X0,sK6(X0,X1),X4)
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X1)
          & m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
          & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( r1_orders_2(X0,X6,sK8(X0,X1,X5,X6))
                  & r1_orders_2(X0,X5,sK8(X0,X1,X5,X6))
                  & r2_hidden(sK8(X0,X1,X5,X6),X1)
                  & m1_subset_1(sK8(X0,X1,X5,X6),u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f40,f43,f42,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  | ~ r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                | ~ r1_orders_2(X0,sK6(X0,X1),X4)
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(X3,X1)
            & r2_hidden(sK6(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_orders_2(X0,X3,X4)
              | ~ r1_orders_2(X0,sK6(X0,X1),X4)
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & r2_hidden(sK6(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r1_orders_2(X0,sK7(X0,X1),X4)
            | ~ r1_orders_2(X0,sK6(X0,X1),X4)
            | ~ r2_hidden(X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X6,X5,X1,X0] :
      ( ? [X7] :
          ( r1_orders_2(X0,X6,X7)
          & r1_orders_2(X0,X5,X7)
          & r2_hidden(X7,X1)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,X6,sK8(X0,X1,X5,X6))
        & r1_orders_2(X0,X5,sK8(X0,X1,X5,X6))
        & r2_hidden(sK8(X0,X1,X5,X6),X1)
        & m1_subset_1(sK8(X0,X1,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    | ~ r1_orders_2(X0,X2,X4)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ? [X7] :
                    ( r1_orders_2(X0,X6,X7)
                    & r1_orders_2(X0,X5,X7)
                    & r2_hidden(X7,X1)
                    & m1_subset_1(X7,u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    | ~ r1_orders_2(X0,X2,X4)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( r1_orders_2(X0,X3,X4)
                    & r1_orders_2(X0,X2,X4)
                    & r2_hidden(X4,X1)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f200,plain,
    ( sP0(sK2,sK3)
    | ~ m1_subset_1(sK6(sK2,sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f199,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f199,plain,
    ( sP0(sK2,sK3)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(sK2,sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f198,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f198,plain,
    ( sP0(sK2,sK3)
    | ~ r2_hidden(sK6(sK2,sK3),sK3)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(sK2,sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f197,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f197,plain,
    ( sP0(sK2,sK3)
    | ~ r2_hidden(sK7(sK2,sK3),sK3)
    | ~ r2_hidden(sK6(sK2,sK3),sK3)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(sK2,sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f196,f103])).

fof(f103,plain,
    ( sP0(sK2,sK3)
    | ~ v1_waybel_0(sK3,sK2) ),
    inference(resolution,[],[f100,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v1_waybel_0(X0,X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f196,plain,
    ( sP0(sK2,sK3)
    | ~ r2_hidden(sK7(sK2,sK3),sK3)
    | ~ r2_hidden(sK6(sK2,sK3),sK3)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(sK2,sK3),u1_struct_0(sK2))
    | v1_waybel_0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f195,f57])).

fof(f195,plain,
    ( sP0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | ~ r2_hidden(sK7(sK2,sK3),sK3)
    | ~ r2_hidden(sK6(sK2,sK3),sK3)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(sK2,sK3),u1_struct_0(sK2))
    | v1_waybel_0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f194,f56])).

fof(f56,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f194,plain,
    ( sP0(sK2,sK3)
    | ~ v1_lattice3(sK2)
    | ~ l1_orders_2(sK2)
    | ~ r2_hidden(sK7(sK2,sK3),sK3)
    | ~ r2_hidden(sK6(sK2,sK3),sK3)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(sK2,sK3),u1_struct_0(sK2))
    | v1_waybel_0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f193,f55])).

fof(f55,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f193,plain,
    ( ~ v5_orders_2(sK2)
    | sP0(sK2,sK3)
    | ~ v1_lattice3(sK2)
    | ~ l1_orders_2(sK2)
    | ~ r2_hidden(sK7(sK2,sK3),sK3)
    | ~ r2_hidden(sK6(sK2,sK3),sK3)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(sK2,sK3),u1_struct_0(sK2))
    | v1_waybel_0(sK3,sK2) ),
    inference(resolution,[],[f192,f60])).

fof(f60,plain,(
    ! [X4,X5] :
      ( r2_hidden(k13_lattice3(sK2,X4,X5),sK3)
      | ~ r2_hidden(X5,sK3)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v1_waybel_0(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ v5_orders_2(X0)
      | sP0(X0,X1)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f191,f72])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X1)
      | ~ r2_hidden(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f190,f73])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X1)
      | ~ r2_hidden(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X1)
      | ~ r2_hidden(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f187,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(superposition,[],[f93,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X1)
      | ~ r2_hidden(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f186,f73])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X1)
      | ~ r2_hidden(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ m1_subset_1(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f185,f72])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X1)
      | ~ m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ r2_hidden(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ m1_subset_1(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X1)
      | ~ m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ r2_hidden(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ m1_subset_1(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f150,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK11(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK11(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK11(X0,X1,X2,X3))
                        & m1_subset_1(sK11(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f52,f53])).

fof(f53,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK11(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK11(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK11(X0,X1,X2,X3))
        & m1_subset_1(sK11(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_0)).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK6(X0,X2),k13_lattice3(X0,X1,sK7(X0,X2)))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(k13_lattice3(X0,X1,sK7(X0,X2)),X2) ) ),
    inference(subsumption_resolution,[],[f149,f73])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK7(X0,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X2)
      | ~ r1_orders_2(X0,sK6(X0,X2),k13_lattice3(X0,X1,sK7(X0,X2)))
      | ~ r2_hidden(k13_lattice3(X0,X1,sK7(X0,X2)),X2) ) ),
    inference(subsumption_resolution,[],[f148,f106])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,X1,sK7(X0,X2)),u1_struct_0(X0))
      | ~ m1_subset_1(sK7(X0,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X2)
      | ~ r1_orders_2(X0,sK6(X0,X2),k13_lattice3(X0,X1,sK7(X0,X2)))
      | ~ r2_hidden(k13_lattice3(X0,X1,sK7(X0,X2)),X2) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,X1,sK7(X0,X2)),u1_struct_0(X0))
      | ~ m1_subset_1(sK7(X0,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X2)
      | ~ r1_orders_2(X0,sK6(X0,X2),k13_lattice3(X0,X1,sK7(X0,X2)))
      | ~ r2_hidden(k13_lattice3(X0,X1,sK7(X0,X2)),X2)
      | ~ m1_subset_1(k13_lattice3(X0,X1,sK7(X0,X2)),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f96,f76])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( ~ r1_orders_2(X0,sK7(X0,X1),X4)
      | sP0(X0,X1)
      | ~ r1_orders_2(X0,sK6(X0,X1),X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f546,plain,(
    ~ v1_waybel_0(sK3,sK2) ),
    inference(resolution,[],[f545,f61])).

fof(f61,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v1_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f545,plain,(
    ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f543,f202])).

fof(f543,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v1_waybel_0(sK3,sK2) ),
    inference(resolution,[],[f542,f62])).

fof(f62,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ v1_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f542,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f541,f201])).

fof(f541,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f540,f204])).

fof(f204,plain,(
    r2_hidden(sK4,sK3) ),
    inference(resolution,[],[f202,f63])).

fof(f63,plain,
    ( ~ v1_waybel_0(sK3,sK2)
    | r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f540,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r2_hidden(sK4,sK3)
    | ~ sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f539,f203])).

fof(f203,plain,(
    r2_hidden(sK5,sK3) ),
    inference(resolution,[],[f202,f64])).

fof(f64,plain,
    ( ~ v1_waybel_0(sK3,sK2)
    | r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f539,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r2_hidden(sK5,sK3)
    | ~ r2_hidden(sK4,sK3)
    | ~ sP0(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f538])).

fof(f538,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r2_hidden(sK5,sK3)
    | ~ r2_hidden(sK4,sK3)
    | ~ sP0(sK2,sK3)
    | ~ r2_hidden(sK5,sK3)
    | ~ r2_hidden(sK4,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ sP0(sK2,sK3) ),
    inference(resolution,[],[f537,f69])).

fof(f69,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(sK8(X0,X1,X5,X6),X1)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f537,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK8(sK2,X0,sK4,sK5),sK3)
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ r2_hidden(sK5,X0)
      | ~ r2_hidden(sK4,X0)
      | ~ sP0(sK2,X0) ) ),
    inference(duplicate_literal_removal,[],[f536])).

fof(f536,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ r2_hidden(sK8(sK2,X0,sK4,sK5),sK3)
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ r2_hidden(sK5,X0)
      | ~ r2_hidden(sK4,X0)
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ sP0(sK2,X0)
      | ~ r2_hidden(sK5,X0)
      | ~ r2_hidden(sK4,X0)
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ sP0(sK2,X0) ) ),
    inference(resolution,[],[f446,f70])).

fof(f70,plain,(
    ! [X6,X0,X5,X1] :
      ( r1_orders_2(X0,X5,sK8(X0,X1,X5,X6))
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f446,plain,(
    ! [X2,X3] :
      ( ~ r1_orders_2(sK2,sK4,sK8(sK2,X2,X3,sK5))
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ r2_hidden(sK8(sK2,X2,X3,sK5),sK3)
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ r2_hidden(sK5,X2)
      | ~ r2_hidden(X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ sP0(sK2,X2) ) ),
    inference(duplicate_literal_removal,[],[f437])).

fof(f437,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ r2_hidden(sK8(sK2,X2,X3,sK5),sK3)
      | ~ r1_orders_2(sK2,sK4,sK8(sK2,X2,X3,sK5))
      | ~ r2_hidden(sK5,X2)
      | ~ r2_hidden(X3,X2)
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ sP0(sK2,X2) ) ),
    inference(resolution,[],[f420,f71])).

fof(f71,plain,(
    ! [X6,X0,X5,X1] :
      ( r1_orders_2(X0,X6,sK8(X0,X1,X5,X6))
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f420,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK2,sK5,X0)
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ r2_hidden(X0,sK3)
      | ~ r1_orders_2(sK2,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f397,f202])).

fof(f397,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK2,sK5,X0)
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ r2_hidden(X0,sK3)
      | ~ r1_orders_2(sK2,sK4,X0)
      | ~ v1_waybel_0(sK3,sK2) ) ),
    inference(resolution,[],[f378,f65])).

fof(f65,plain,
    ( ~ r2_hidden(k13_lattice3(sK2,sK4,sK5),sK3)
    | ~ v1_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f378,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k13_lattice3(sK2,X0,X2),sK3)
      | ~ r1_orders_2(sK2,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X1,sK3)
      | ~ r1_orders_2(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f377,f55])).

fof(f377,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | ~ r1_orders_2(sK2,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X1,sK3)
      | r2_hidden(k13_lattice3(sK2,X0,X2),sK3)
      | ~ v5_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f376,f56])).

fof(f376,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | ~ r1_orders_2(sK2,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X1,sK3)
      | r2_hidden(k13_lattice3(sK2,X0,X2),sK3)
      | ~ v1_lattice3(sK2)
      | ~ v5_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f375,f57])).

fof(f375,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | ~ r1_orders_2(sK2,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X1,sK3)
      | r2_hidden(k13_lattice3(sK2,X0,X2),sK3)
      | ~ l1_orders_2(sK2)
      | ~ v1_lattice3(sK2)
      | ~ v5_orders_2(sK2) ) ),
    inference(duplicate_literal_removal,[],[f361])).

fof(f361,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | ~ r1_orders_2(sK2,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X1,sK3)
      | r2_hidden(k13_lattice3(sK2,X0,X2),sK3)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ v1_lattice3(sK2)
      | ~ v5_orders_2(sK2) ) ),
    inference(resolution,[],[f360,f106])).

fof(f360,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(k13_lattice3(sK2,X7,X5),u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X7,X6)
      | ~ r1_orders_2(sK2,X5,X6)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | ~ m1_subset_1(X7,u1_struct_0(sK2))
      | ~ r2_hidden(X6,sK3)
      | r2_hidden(k13_lattice3(sK2,X7,X5),sK3) ) ),
    inference(subsumption_resolution,[],[f359,f101])).

fof(f101,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f94,f59])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f359,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_orders_2(sK2,X5,X6)
      | ~ r1_orders_2(sK2,X7,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK2))
      | ~ m1_subset_1(k13_lattice3(sK2,X7,X5),u1_struct_0(sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | ~ m1_subset_1(X7,u1_struct_0(sK2))
      | ~ r2_hidden(X6,sK3)
      | r2_hidden(k13_lattice3(sK2,X7,X5),sK3) ) ),
    inference(subsumption_resolution,[],[f358,f55])).

fof(f358,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_orders_2(sK2,X5,X6)
      | ~ r1_orders_2(sK2,X7,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK2))
      | ~ m1_subset_1(k13_lattice3(sK2,X7,X5),u1_struct_0(sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | ~ m1_subset_1(X7,u1_struct_0(sK2))
      | ~ v5_orders_2(sK2)
      | ~ r2_hidden(X6,sK3)
      | r2_hidden(k13_lattice3(sK2,X7,X5),sK3) ) ),
    inference(subsumption_resolution,[],[f357,f56])).

fof(f357,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_orders_2(sK2,X5,X6)
      | ~ r1_orders_2(sK2,X7,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK2))
      | ~ m1_subset_1(k13_lattice3(sK2,X7,X5),u1_struct_0(sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | ~ m1_subset_1(X7,u1_struct_0(sK2))
      | ~ v1_lattice3(sK2)
      | ~ v5_orders_2(sK2)
      | ~ r2_hidden(X6,sK3)
      | r2_hidden(k13_lattice3(sK2,X7,X5),sK3) ) ),
    inference(subsumption_resolution,[],[f353,f57])).

fof(f353,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_orders_2(sK2,X5,X6)
      | ~ r1_orders_2(sK2,X7,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK2))
      | ~ m1_subset_1(k13_lattice3(sK2,X7,X5),u1_struct_0(sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | ~ m1_subset_1(X7,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ v1_lattice3(sK2)
      | ~ v5_orders_2(sK2)
      | ~ r2_hidden(X6,sK3)
      | r2_hidden(k13_lattice3(sK2,X7,X5),sK3) ) ),
    inference(duplicate_literal_removal,[],[f344])).

fof(f344,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_orders_2(sK2,X5,X6)
      | ~ r1_orders_2(sK2,X7,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK2))
      | ~ m1_subset_1(k13_lattice3(sK2,X7,X5),u1_struct_0(sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | ~ m1_subset_1(X7,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ v1_lattice3(sK2)
      | ~ v5_orders_2(sK2)
      | ~ r2_hidden(X6,sK3)
      | ~ m1_subset_1(k13_lattice3(sK2,X7,X5),u1_struct_0(sK2))
      | ~ m1_subset_1(X6,u1_struct_0(sK2))
      | r2_hidden(k13_lattice3(sK2,X7,X5),sK3) ) ),
    inference(resolution,[],[f95,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_hidden(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f120,f57])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_hidden(X0,sK3)
      | ~ l1_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f119,f58])).

fof(f58,plain,(
    v12_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ v12_waybel_0(sK3,sK2)
      | r2_hidden(X0,sK3)
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f78,f59])).

fof(f78,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_orders_2(X0,X5,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v12_waybel_0(X1,X0)
      | r2_hidden(X5,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK10(X0,X1),X1)
                & r1_orders_2(X0,sK10(X0,X1),sK9(X0,X1))
                & r2_hidden(sK9(X0,X1),X1)
                & m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f46,f48,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X3,X2)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,X3,sK9(X0,X1))
            & r2_hidden(sK9(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X3,sK9(X0,X1))
          & r2_hidden(sK9(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK10(X0,X1),X1)
        & r1_orders_2(X0,sK10(X0,X1),sK9(X0,X1))
        & r2_hidden(sK9(X0,X1),X1)
        & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X3,X2)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_waybel_0)).

fof(f95,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,k13_lattice3(X0,X1,X2),X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

%------------------------------------------------------------------------------
