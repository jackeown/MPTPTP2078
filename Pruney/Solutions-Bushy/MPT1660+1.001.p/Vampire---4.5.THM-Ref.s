%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1660+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:17 EST 2020

% Result     : Theorem 0.94s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  133 (1799 expanded)
%              Number of leaves         :   17 ( 642 expanded)
%              Depth                    :   45
%              Number of atoms          : 1055 (22338 expanded)
%              Number of equality atoms :   14 ( 156 expanded)
%              Maximal formula depth    :   17 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f431,plain,(
    $false ),
    inference(subsumption_resolution,[],[f430,f168])).

fof(f168,plain,(
    v1_waybel_0(sK3,sK2) ),
    inference(resolution,[],[f167,f89])).

fof(f89,plain,
    ( ~ sP0(sK2,sK3)
    | v1_waybel_0(sK3,sK2) ),
    inference(resolution,[],[f88,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v1_waybel_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v1_waybel_0(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v1_waybel_0(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ( ( v1_waybel_0(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v1_waybel_0(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ( v1_waybel_0(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f88,plain,(
    sP1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f87,f48])).

fof(f48,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f26,f25,f24,f23])).

fof(f23,plain,
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

% (30271)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f24,plain,
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

fof(f25,plain,
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

fof(f26,plain,
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

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_waybel_0)).

fof(f87,plain,
    ( sP1(sK3,sK2)
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f68,f50])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f10,f18,f17])).

fof(f17,plain,(
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

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_waybel_0)).

fof(f167,plain,(
    sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f166,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f31,f34,f33,f32])).

fof(f32,plain,(
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

fof(f33,plain,(
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

fof(f34,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f166,plain,
    ( sP0(sK2,sK3)
    | ~ m1_subset_1(sK6(sK2,sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f165,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f165,plain,
    ( sP0(sK2,sK3)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(sK2,sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f164,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f164,plain,
    ( sP0(sK2,sK3)
    | ~ r2_hidden(sK6(sK2,sK3),sK3)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(sK2,sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f163,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f163,plain,
    ( sP0(sK2,sK3)
    | ~ r2_hidden(sK7(sK2,sK3),sK3)
    | ~ r2_hidden(sK6(sK2,sK3),sK3)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(sK2,sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f162,f90])).

fof(f90,plain,
    ( sP0(sK2,sK3)
    | ~ v1_waybel_0(sK3,sK2) ),
    inference(resolution,[],[f88,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v1_waybel_0(X0,X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f162,plain,
    ( sP0(sK2,sK3)
    | ~ r2_hidden(sK7(sK2,sK3),sK3)
    | ~ r2_hidden(sK6(sK2,sK3),sK3)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(sK2,sK3),u1_struct_0(sK2))
    | v1_waybel_0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f161,f48])).

fof(f161,plain,
    ( sP0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | ~ r2_hidden(sK7(sK2,sK3),sK3)
    | ~ r2_hidden(sK6(sK2,sK3),sK3)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(sK2,sK3),u1_struct_0(sK2))
    | v1_waybel_0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f160,f47])).

fof(f47,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f160,plain,
    ( sP0(sK2,sK3)
    | ~ v1_lattice3(sK2)
    | ~ l1_orders_2(sK2)
    | ~ r2_hidden(sK7(sK2,sK3),sK3)
    | ~ r2_hidden(sK6(sK2,sK3),sK3)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(sK2,sK3),u1_struct_0(sK2))
    | v1_waybel_0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f159,f46])).

fof(f46,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f159,plain,
    ( ~ v5_orders_2(sK2)
    | sP0(sK2,sK3)
    | ~ v1_lattice3(sK2)
    | ~ l1_orders_2(sK2)
    | ~ r2_hidden(sK7(sK2,sK3),sK3)
    | ~ r2_hidden(sK6(sK2,sK3),sK3)
    | ~ m1_subset_1(sK7(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(sK2,sK3),u1_struct_0(sK2))
    | v1_waybel_0(sK3,sK2) ),
    inference(resolution,[],[f158,f51])).

fof(f51,plain,(
    ! [X4,X5] :
      ( r2_hidden(k13_lattice3(sK2,X4,X5),sK3)
      | ~ r2_hidden(X5,sK3)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v1_waybel_0(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ v5_orders_2(X0)
      | sP0(X0,X1)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f157,f63])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X1)
      | ~ r2_hidden(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f156,f64])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X1)
      | ~ r2_hidden(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
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
    inference(resolution,[],[f154,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k13_lattice3)).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X1)
      | ~ r2_hidden(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f153,f64])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X1)
      | ~ r2_hidden(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ m1_subset_1(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f152,f63])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X1)
      | ~ m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ r2_hidden(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ m1_subset_1(k13_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,(
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
    inference(resolution,[],[f114,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f43,f44])).

fof(f44,plain,(
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

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_0)).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK6(X0,X2),k13_lattice3(X0,X1,sK7(X0,X2)))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(k13_lattice3(X0,X1,sK7(X0,X2)),X2) ) ),
    inference(subsumption_resolution,[],[f113,f64])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK7(X0,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X2)
      | ~ r1_orders_2(X0,sK6(X0,X2),k13_lattice3(X0,X1,sK7(X0,X2)))
      | ~ r2_hidden(k13_lattice3(X0,X1,sK7(X0,X2)),X2) ) ),
    inference(subsumption_resolution,[],[f112,f82])).

fof(f112,plain,(
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
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
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
    inference(resolution,[],[f84,f67])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( ~ r1_orders_2(X0,sK7(X0,X1),X4)
      | sP0(X0,X1)
      | ~ r1_orders_2(X0,sK6(X0,X1),X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f430,plain,(
    ~ v1_waybel_0(sK3,sK2) ),
    inference(resolution,[],[f429,f52])).

fof(f52,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v1_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f429,plain,(
    ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f428,f168])).

fof(f428,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v1_waybel_0(sK3,sK2) ),
    inference(resolution,[],[f427,f53])).

fof(f53,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ v1_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f427,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f426,f167])).

fof(f426,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f425,f169])).

fof(f169,plain,(
    r2_hidden(sK5,sK3) ),
    inference(resolution,[],[f168,f55])).

fof(f55,plain,
    ( ~ v1_waybel_0(sK3,sK2)
    | r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f425,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r2_hidden(sK5,sK3)
    | ~ sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f424,f170])).

fof(f170,plain,(
    r2_hidden(sK4,sK3) ),
    inference(resolution,[],[f168,f54])).

fof(f54,plain,
    ( ~ v1_waybel_0(sK3,sK2)
    | r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f424,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r2_hidden(sK4,sK3)
    | ~ r2_hidden(sK5,sK3)
    | ~ sP0(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f423])).

fof(f423,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r2_hidden(sK4,sK3)
    | ~ r2_hidden(sK5,sK3)
    | ~ sP0(sK2,sK3)
    | ~ r2_hidden(sK4,sK3)
    | ~ r2_hidden(sK5,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ sP0(sK2,sK3) ),
    inference(resolution,[],[f422,f60])).

fof(f60,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(sK8(X0,X1,X5,X6),X1)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f422,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK8(sK2,X0,sK5,sK4),sK3)
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ r2_hidden(sK4,X0)
      | ~ r2_hidden(sK5,X0)
      | ~ sP0(sK2,X0) ) ),
    inference(duplicate_literal_removal,[],[f421])).

fof(f421,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ r2_hidden(sK8(sK2,X0,sK5,sK4),sK3)
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ r2_hidden(sK4,X0)
      | ~ r2_hidden(sK5,X0)
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ sP0(sK2,X0)
      | ~ r2_hidden(sK4,X0)
      | ~ r2_hidden(sK5,X0)
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ sP0(sK2,X0) ) ),
    inference(resolution,[],[f351,f62])).

fof(f62,plain,(
    ! [X6,X0,X5,X1] :
      ( r1_orders_2(X0,X6,sK8(X0,X1,X5,X6))
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f351,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK2,sK4,sK8(sK2,X0,sK5,X1))
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ r2_hidden(sK8(sK2,X0,sK5,X1),sK3)
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(sK5,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ sP0(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f350,f59])).

fof(f59,plain,(
    ! [X6,X0,X5,X1] :
      ( m1_subset_1(sK8(X0,X1,X5,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

% (30254)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f350,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK8(sK2,X0,sK5,X1),u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ r2_hidden(sK8(sK2,X0,sK5,X1),sK3)
      | ~ r1_orders_2(sK2,sK4,sK8(sK2,X0,sK5,X1))
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(sK5,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ sP0(sK2,X0) ) ),
    inference(duplicate_literal_removal,[],[f339])).

fof(f339,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK8(sK2,X0,sK5,X1),u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ r2_hidden(sK8(sK2,X0,sK5,X1),sK3)
      | ~ r1_orders_2(sK2,sK4,sK8(sK2,X0,sK5,X1))
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(sK5,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ sP0(sK2,X0) ) ),
    inference(resolution,[],[f338,f61])).

fof(f61,plain,(
    ! [X6,X0,X5,X1] :
      ( r1_orders_2(X0,X5,sK8(X0,X1,X5,X6))
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f338,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK2,sK5,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ r2_hidden(X0,sK3)
      | ~ r1_orders_2(sK2,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f319,f168])).

fof(f319,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,sK5,X0)
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ r2_hidden(X0,sK3)
      | ~ r1_orders_2(sK2,sK4,X0)
      | ~ v1_waybel_0(sK3,sK2) ) ),
    inference(resolution,[],[f318,f56])).

fof(f56,plain,
    ( ~ r2_hidden(k13_lattice3(sK2,sK4,sK5),sK3)
    | ~ v1_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f318,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k13_lattice3(sK2,X0,X2),sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X1,sK3)
      | ~ r1_orders_2(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f317,f46])).

fof(f317,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X1,sK3)
      | r2_hidden(k13_lattice3(sK2,X0,X2),sK3)
      | ~ v5_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f316,f47])).

fof(f316,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X1,sK3)
      | r2_hidden(k13_lattice3(sK2,X0,X2),sK3)
      | ~ v1_lattice3(sK2)
      | ~ v5_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f315,f48])).

fof(f315,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X1,sK3)
      | r2_hidden(k13_lattice3(sK2,X0,X2),sK3)
      | ~ l1_orders_2(sK2)
      | ~ v1_lattice3(sK2)
      | ~ v5_orders_2(sK2) ) ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
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
    inference(resolution,[],[f301,f82])).

fof(f301,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(k13_lattice3(sK2,X11,X9),u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X11,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X9,X10)
      | ~ m1_subset_1(X9,u1_struct_0(sK2))
      | ~ m1_subset_1(X11,u1_struct_0(sK2))
      | ~ r2_hidden(X10,sK3)
      | r2_hidden(k13_lattice3(sK2,X11,X9),sK3) ) ),
    inference(subsumption_resolution,[],[f300,f46])).

fof(f300,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_orders_2(sK2,X9,X10)
      | ~ r1_orders_2(sK2,X11,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK2))
      | ~ m1_subset_1(k13_lattice3(sK2,X11,X9),u1_struct_0(sK2))
      | ~ m1_subset_1(X9,u1_struct_0(sK2))
      | ~ m1_subset_1(X11,u1_struct_0(sK2))
      | ~ v5_orders_2(sK2)
      | ~ r2_hidden(X10,sK3)
      | r2_hidden(k13_lattice3(sK2,X11,X9),sK3) ) ),
    inference(subsumption_resolution,[],[f299,f47])).

fof(f299,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_orders_2(sK2,X9,X10)
      | ~ r1_orders_2(sK2,X11,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK2))
      | ~ m1_subset_1(k13_lattice3(sK2,X11,X9),u1_struct_0(sK2))
      | ~ m1_subset_1(X9,u1_struct_0(sK2))
      | ~ m1_subset_1(X11,u1_struct_0(sK2))
      | ~ v1_lattice3(sK2)
      | ~ v5_orders_2(sK2)
      | ~ r2_hidden(X10,sK3)
      | r2_hidden(k13_lattice3(sK2,X11,X9),sK3) ) ),
    inference(subsumption_resolution,[],[f291,f48])).

fof(f291,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_orders_2(sK2,X9,X10)
      | ~ r1_orders_2(sK2,X11,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK2))
      | ~ m1_subset_1(k13_lattice3(sK2,X11,X9),u1_struct_0(sK2))
      | ~ m1_subset_1(X9,u1_struct_0(sK2))
      | ~ m1_subset_1(X11,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ v1_lattice3(sK2)
      | ~ v5_orders_2(sK2)
      | ~ r2_hidden(X10,sK3)
      | r2_hidden(k13_lattice3(sK2,X11,X9),sK3) ) ),
    inference(duplicate_literal_removal,[],[f286])).

fof(f286,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_orders_2(sK2,X9,X10)
      | ~ r1_orders_2(sK2,X11,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK2))
      | ~ m1_subset_1(k13_lattice3(sK2,X11,X9),u1_struct_0(sK2))
      | ~ m1_subset_1(X9,u1_struct_0(sK2))
      | ~ m1_subset_1(X11,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ v1_lattice3(sK2)
      | ~ v5_orders_2(sK2)
      | ~ r2_hidden(X10,sK3)
      | ~ m1_subset_1(k13_lattice3(sK2,X11,X9),u1_struct_0(sK2))
      | ~ m1_subset_1(X10,u1_struct_0(sK2))
      | r2_hidden(k13_lattice3(sK2,X11,X9),sK3) ) ),
    inference(resolution,[],[f83,f98])).

% (30267)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_hidden(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f97,f48])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_hidden(X0,sK3)
      | ~ l1_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f96,f49])).

fof(f49,plain,(
    v12_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ v12_waybel_0(sK3,sK2)
      | r2_hidden(X0,sK3)
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f69,f50])).

fof(f69,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_orders_2(X0,X5,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v12_waybel_0(X1,X0)
      | r2_hidden(X5,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f37,f39,f38])).

fof(f38,plain,(
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

fof(f39,plain,(
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

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_waybel_0)).

fof(f83,plain,(
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
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f45])).

%------------------------------------------------------------------------------
