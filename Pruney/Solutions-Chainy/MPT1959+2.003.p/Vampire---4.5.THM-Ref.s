%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:50 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 364 expanded)
%              Number of leaves         :   34 ( 122 expanded)
%              Depth                    :   13
%              Number of atoms          :  605 (2778 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f313,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f90,f106,f124,f126,f131,f134,f180,f191,f208,f250,f252,f258,f268,f279,f282,f285,f306,f308,f312])).

fof(f312,plain,
    ( ~ spl7_2
    | spl7_5 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | ~ spl7_2
    | spl7_5 ),
    inference(resolution,[],[f310,f88])).

fof(f88,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl7_2
  <=> r2_hidden(k3_yellow_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f310,plain,
    ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | spl7_5 ),
    inference(resolution,[],[f122,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f122,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK2),sK3)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl7_5
  <=> m1_subset_1(k3_yellow_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f308,plain,(
    spl7_15 ),
    inference(avatar_contradiction_clause,[],[f307])).

fof(f307,plain,
    ( $false
    | spl7_15 ),
    inference(resolution,[],[f254,f52])).

fof(f52,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( r2_hidden(k3_yellow_0(sK2),sK3)
      | ~ v1_subset_1(sK3,u1_struct_0(sK2)) )
    & ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
      | v1_subset_1(sK3,u1_struct_0(sK2)) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v13_waybel_0(sK3,sK2)
    & v2_waybel_0(sK3,sK2)
    & ~ v1_xboole_0(sK3)
    & l1_orders_2(sK2)
    & v1_yellow_0(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK2),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK2)) )
          & ( ~ r2_hidden(k3_yellow_0(sK2),X1)
            | v1_subset_1(X1,u1_struct_0(sK2)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & v13_waybel_0(X1,sK2)
          & v2_waybel_0(X1,sK2)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK2)
      & v1_yellow_0(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ( r2_hidden(k3_yellow_0(sK2),X1)
          | ~ v1_subset_1(X1,u1_struct_0(sK2)) )
        & ( ~ r2_hidden(k3_yellow_0(sK2),X1)
          | v1_subset_1(X1,u1_struct_0(sK2)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & v13_waybel_0(X1,sK2)
        & v2_waybel_0(X1,sK2)
        & ~ v1_xboole_0(X1) )
   => ( ( r2_hidden(k3_yellow_0(sK2),sK3)
        | ~ v1_subset_1(sK3,u1_struct_0(sK2)) )
      & ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
        | v1_subset_1(sK3,u1_struct_0(sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & v13_waybel_0(sK3,sK2)
      & v2_waybel_0(sK3,sK2)
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f254,plain,
    ( ~ l1_orders_2(sK2)
    | spl7_15 ),
    inference(resolution,[],[f246,f61])).

fof(f61,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f246,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl7_15
  <=> m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f306,plain,
    ( ~ spl7_9
    | spl7_10
    | ~ spl7_17 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | ~ spl7_9
    | spl7_10
    | ~ spl7_17 ),
    inference(resolution,[],[f297,f179])).

fof(f179,plain,
    ( ~ r2_hidden(sK6(u1_struct_0(sK2),sK3),sK3)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl7_10
  <=> r2_hidden(sK6(u1_struct_0(sK2),sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f297,plain,
    ( r2_hidden(sK6(u1_struct_0(sK2),sK3),sK3)
    | ~ spl7_9
    | ~ spl7_17 ),
    inference(resolution,[],[f288,f174])).

fof(f174,plain,
    ( r2_hidden(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl7_9
  <=> r2_hidden(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK2))
        | r2_hidden(X0,sK3) )
    | ~ spl7_17 ),
    inference(resolution,[],[f263,f73])).

fof(f263,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r2_hidden(X0,sK3) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl7_17
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r2_hidden(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f285,plain,(
    spl7_19 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | spl7_19 ),
    inference(resolution,[],[f274,f56])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f274,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_19 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl7_19
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f282,plain,(
    spl7_20 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | spl7_20 ),
    inference(resolution,[],[f278,f55])).

fof(f55,plain,(
    v13_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f278,plain,
    ( ~ v13_waybel_0(sK3,sK2)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl7_20
  <=> v13_waybel_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f279,plain,
    ( ~ spl7_19
    | ~ spl7_20
    | spl7_18 ),
    inference(avatar_split_clause,[],[f269,f265,f276,f272])).

fof(f265,plain,
    ( spl7_18
  <=> sP0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f269,plain,
    ( ~ v13_waybel_0(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_18 ),
    inference(resolution,[],[f267,f97])).

fof(f97,plain,(
    ! [X1] :
      ( sP0(X1,sK2)
      | ~ v13_waybel_0(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f95,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v13_waybel_0(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v13_waybel_0(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f95,plain,(
    ! [X0] :
      ( sP1(sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f70,f52])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f18,f30,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r1_orders_2(X0,X2,X3)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f267,plain,
    ( ~ sP0(sK3,sK2)
    | spl7_18 ),
    inference(avatar_component_clause,[],[f265])).

fof(f268,plain,
    ( spl7_17
    | ~ spl7_18
    | ~ spl7_5
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f259,f248,f121,f265,f262])).

fof(f248,plain,
    ( spl7_16
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k3_yellow_0(sK2),X0)
        | ~ sP0(X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ sP0(sK3,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r2_hidden(X0,sK3) )
    | ~ spl7_5
    | ~ spl7_16 ),
    inference(resolution,[],[f249,f128])).

fof(f128,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f123,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK3)
      | r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f74,f53])).

fof(f53,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f123,plain,
    ( m1_subset_1(k3_yellow_0(sK2),sK3)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k3_yellow_0(sK2),X0)
        | ~ sP0(X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r2_hidden(X1,X0) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f248])).

fof(f258,plain,(
    ~ spl7_13 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl7_13 ),
    inference(resolution,[],[f238,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f238,plain,
    ( v2_struct_0(sK2)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl7_13
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f252,plain,(
    spl7_14 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | spl7_14 ),
    inference(resolution,[],[f242,f50])).

fof(f50,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f242,plain,
    ( ~ v5_orders_2(sK2)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl7_14
  <=> v5_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f250,plain,
    ( spl7_13
    | ~ spl7_14
    | ~ spl7_4
    | ~ spl7_15
    | spl7_16 ),
    inference(avatar_split_clause,[],[f234,f248,f244,f117,f240,f236])).

fof(f117,plain,
    ( spl7_4
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f234,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k3_yellow_0(sK2),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2))
      | ~ sP0(X0,sK2)
      | ~ l1_orders_2(sK2)
      | r2_hidden(X1,X0)
      | ~ v5_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f213,f51])).

fof(f51,plain,(
    v1_yellow_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f213,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_yellow_0(X5)
      | ~ r2_hidden(k3_yellow_0(X5),X4)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | ~ m1_subset_1(k3_yellow_0(X5),u1_struct_0(X5))
      | ~ sP0(X4,X5)
      | ~ l1_orders_2(X5)
      | r2_hidden(X3,X4)
      | ~ v5_orders_2(X5)
      | v2_struct_0(X5) ) ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X3,X4)
      | ~ r2_hidden(k3_yellow_0(X5),X4)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | ~ m1_subset_1(k3_yellow_0(X5),u1_struct_0(X5))
      | ~ sP0(X4,X5)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | ~ v1_yellow_0(X5)
      | ~ v5_orders_2(X5)
      | v2_struct_0(X5) ) ),
    inference(resolution,[],[f64,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f64,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r1_orders_2(X1,X4,X5)
      | r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X0)
          & r1_orders_2(X1,sK4(X0,X1),sK5(X0,X1))
          & r2_hidden(sK4(X0,X1),X0)
          & m1_subset_1(sK5(X0,X1),u1_struct_0(X1))
          & m1_subset_1(sK4(X0,X1),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r1_orders_2(X1,X4,X5)
                | ~ r2_hidden(X4,X0)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f39,f41,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X0)
              & r1_orders_2(X1,X2,X3)
              & r2_hidden(X2,X0)
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X0)
            & r1_orders_2(X1,sK4(X0,X1),X3)
            & r2_hidden(sK4(X0,X1),X0)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r1_orders_2(X1,sK4(X0,X1),X3)
          & r2_hidden(sK4(X0,X1),X0)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_hidden(sK5(X0,X1),X0)
        & r1_orders_2(X1,sK4(X0,X1),sK5(X0,X1))
        & r2_hidden(sK4(X0,X1),X0)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X0)
                & r1_orders_2(X1,X2,X3)
                & r2_hidden(X2,X0)
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r1_orders_2(X1,X4,X5)
                | ~ r2_hidden(X4,X0)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
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
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f208,plain,
    ( spl7_9
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | spl7_9
    | ~ spl7_10 ),
    inference(resolution,[],[f205,f194])).

fof(f194,plain,
    ( ~ m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | spl7_9 ),
    inference(resolution,[],[f175,f148])).

fof(f148,plain,(
    ! [X0] :
      ( r2_hidden(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f143,f56])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f93,f53])).

fof(f93,plain,(
    ! [X2,X3,X1] :
      ( v1_xboole_0(X3)
      | ~ m1_subset_1(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f74,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f175,plain,
    ( ~ r2_hidden(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f173])).

fof(f205,plain,
    ( m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ spl7_10 ),
    inference(resolution,[],[f193,f56])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | m1_subset_1(sK6(u1_struct_0(sK2),sK3),X0) )
    | ~ spl7_10 ),
    inference(resolution,[],[f178,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f178,plain,
    ( r2_hidden(sK6(u1_struct_0(sK2),sK3),sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f177])).

fof(f191,plain,
    ( spl7_9
    | spl7_3
    | spl7_10 ),
    inference(avatar_split_clause,[],[f190,f177,f103,f173])).

fof(f103,plain,
    ( spl7_3
  <=> u1_struct_0(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f190,plain,
    ( u1_struct_0(sK2) = sK3
    | r2_hidden(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | spl7_10 ),
    inference(resolution,[],[f179,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK6(X0,X1),X1)
          | ~ r2_hidden(sK6(X0,X1),X0) )
        & ( r2_hidden(sK6(X0,X1),X1)
          | r2_hidden(sK6(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1),X1)
          | ~ r2_hidden(sK6(X0,X1),X0) )
        & ( r2_hidden(sK6(X0,X1),X1)
          | r2_hidden(sK6(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f180,plain,
    ( ~ spl7_9
    | ~ spl7_10
    | spl7_3 ),
    inference(avatar_split_clause,[],[f167,f103,f177,f173])).

fof(f167,plain,
    ( ~ r2_hidden(sK6(u1_struct_0(sK2),sK3),sK3)
    | ~ r2_hidden(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | spl7_3 ),
    inference(extensionality_resolution,[],[f78,f104])).

fof(f104,plain,
    ( u1_struct_0(sK2) != sK3
    | spl7_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | X0 = X1
      | ~ r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f134,plain,
    ( ~ spl7_1
    | ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(resolution,[],[f132,f91])).

fof(f91,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f59,f60])).

fof(f60,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f59,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f132,plain,
    ( v1_subset_1(sK3,sK3)
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f83,f105])).

fof(f105,plain,
    ( u1_struct_0(sK2) = sK3
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f83,plain,
    ( v1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl7_1
  <=> v1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f131,plain,
    ( spl7_2
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl7_2
    | ~ spl7_5 ),
    inference(resolution,[],[f128,f87])).

fof(f87,plain,
    ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f126,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl7_4 ),
    inference(resolution,[],[f119,f52])).

fof(f119,plain,
    ( ~ l1_orders_2(sK2)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f124,plain,
    ( ~ spl7_4
    | spl7_5
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f115,f103,f121,f117])).

fof(f115,plain,
    ( m1_subset_1(k3_yellow_0(sK2),sK3)
    | ~ l1_orders_2(sK2)
    | ~ spl7_3 ),
    inference(superposition,[],[f61,f105])).

fof(f106,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f101,f103,f82])).

fof(f101,plain,
    ( u1_struct_0(sK2) = sK3
    | v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f76,f56])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f90,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f57,f86,f82])).

fof(f57,plain,
    ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f58,f86,f82])).

fof(f58,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.16/0.36  % Computer   : n008.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 10:28:30 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.23/0.52  % (12701)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.52  % (12720)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.52  % (12712)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.53  % (12728)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.23/0.53  % (12718)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.54  % (12706)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.54  % (12710)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.29/0.55  % (12703)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.55  % (12712)Refutation found. Thanks to Tanya!
% 1.29/0.55  % SZS status Theorem for theBenchmark
% 1.29/0.55  % SZS output start Proof for theBenchmark
% 1.29/0.55  fof(f313,plain,(
% 1.29/0.55    $false),
% 1.29/0.55    inference(avatar_sat_refutation,[],[f89,f90,f106,f124,f126,f131,f134,f180,f191,f208,f250,f252,f258,f268,f279,f282,f285,f306,f308,f312])).
% 1.29/0.55  fof(f312,plain,(
% 1.29/0.55    ~spl7_2 | spl7_5),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f311])).
% 1.29/0.55  fof(f311,plain,(
% 1.29/0.55    $false | (~spl7_2 | spl7_5)),
% 1.29/0.55    inference(resolution,[],[f310,f88])).
% 1.29/0.55  fof(f88,plain,(
% 1.29/0.55    r2_hidden(k3_yellow_0(sK2),sK3) | ~spl7_2),
% 1.29/0.55    inference(avatar_component_clause,[],[f86])).
% 1.29/0.55  fof(f86,plain,(
% 1.29/0.55    spl7_2 <=> r2_hidden(k3_yellow_0(sK2),sK3)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.29/0.55  fof(f310,plain,(
% 1.29/0.55    ~r2_hidden(k3_yellow_0(sK2),sK3) | spl7_5),
% 1.29/0.55    inference(resolution,[],[f122,f73])).
% 1.29/0.55  fof(f73,plain,(
% 1.29/0.55    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f22])).
% 1.29/0.55  fof(f22,plain,(
% 1.29/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.29/0.55    inference(ennf_transformation,[],[f5])).
% 1.29/0.55  fof(f5,axiom,(
% 1.29/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.29/0.55  fof(f122,plain,(
% 1.29/0.55    ~m1_subset_1(k3_yellow_0(sK2),sK3) | spl7_5),
% 1.29/0.55    inference(avatar_component_clause,[],[f121])).
% 1.29/0.55  fof(f121,plain,(
% 1.29/0.55    spl7_5 <=> m1_subset_1(k3_yellow_0(sK2),sK3)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.29/0.55  fof(f308,plain,(
% 1.29/0.55    spl7_15),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f307])).
% 1.29/0.55  fof(f307,plain,(
% 1.29/0.55    $false | spl7_15),
% 1.29/0.55    inference(resolution,[],[f254,f52])).
% 1.29/0.55  fof(f52,plain,(
% 1.29/0.55    l1_orders_2(sK2)),
% 1.29/0.55    inference(cnf_transformation,[],[f36])).
% 1.29/0.55  fof(f36,plain,(
% 1.29/0.55    ((r2_hidden(k3_yellow_0(sK2),sK3) | ~v1_subset_1(sK3,u1_struct_0(sK2))) & (~r2_hidden(k3_yellow_0(sK2),sK3) | v1_subset_1(sK3,u1_struct_0(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v13_waybel_0(sK3,sK2) & v2_waybel_0(sK3,sK2) & ~v1_xboole_0(sK3)) & l1_orders_2(sK2) & v1_yellow_0(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 1.29/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f35,f34])).
% 1.29/0.55  fof(f34,plain,(
% 1.29/0.55    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK2),X1) | ~v1_subset_1(X1,u1_struct_0(sK2))) & (~r2_hidden(k3_yellow_0(sK2),X1) | v1_subset_1(X1,u1_struct_0(sK2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v13_waybel_0(X1,sK2) & v2_waybel_0(X1,sK2) & ~v1_xboole_0(X1)) & l1_orders_2(sK2) & v1_yellow_0(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 1.29/0.55    introduced(choice_axiom,[])).
% 1.29/0.55  fof(f35,plain,(
% 1.29/0.55    ? [X1] : ((r2_hidden(k3_yellow_0(sK2),X1) | ~v1_subset_1(X1,u1_struct_0(sK2))) & (~r2_hidden(k3_yellow_0(sK2),X1) | v1_subset_1(X1,u1_struct_0(sK2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v13_waybel_0(X1,sK2) & v2_waybel_0(X1,sK2) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK2),sK3) | ~v1_subset_1(sK3,u1_struct_0(sK2))) & (~r2_hidden(k3_yellow_0(sK2),sK3) | v1_subset_1(sK3,u1_struct_0(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v13_waybel_0(sK3,sK2) & v2_waybel_0(sK3,sK2) & ~v1_xboole_0(sK3))),
% 1.29/0.55    introduced(choice_axiom,[])).
% 1.29/0.55  fof(f33,plain,(
% 1.29/0.55    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.29/0.55    inference(flattening,[],[f32])).
% 1.29/0.55  fof(f32,plain,(
% 1.29/0.55    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.29/0.55    inference(nnf_transformation,[],[f15])).
% 1.29/0.55  fof(f15,plain,(
% 1.29/0.55    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.29/0.55    inference(flattening,[],[f14])).
% 1.29/0.55  fof(f14,plain,(
% 1.29/0.55    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.29/0.55    inference(ennf_transformation,[],[f13])).
% 1.29/0.55  fof(f13,negated_conjecture,(
% 1.29/0.55    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.29/0.55    inference(negated_conjecture,[],[f12])).
% 1.29/0.55  fof(f12,conjecture,(
% 1.29/0.55    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 1.29/0.55  fof(f254,plain,(
% 1.29/0.55    ~l1_orders_2(sK2) | spl7_15),
% 1.29/0.55    inference(resolution,[],[f246,f61])).
% 1.29/0.55  fof(f61,plain,(
% 1.29/0.55    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f16])).
% 1.29/0.55  fof(f16,plain,(
% 1.29/0.55    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.29/0.55    inference(ennf_transformation,[],[f8])).
% 1.29/0.55  fof(f8,axiom,(
% 1.29/0.55    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 1.29/0.55  fof(f246,plain,(
% 1.29/0.55    ~m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2)) | spl7_15),
% 1.29/0.55    inference(avatar_component_clause,[],[f244])).
% 1.29/0.55  fof(f244,plain,(
% 1.29/0.55    spl7_15 <=> m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.29/0.55  fof(f306,plain,(
% 1.29/0.55    ~spl7_9 | spl7_10 | ~spl7_17),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f303])).
% 1.29/0.55  fof(f303,plain,(
% 1.29/0.55    $false | (~spl7_9 | spl7_10 | ~spl7_17)),
% 1.29/0.55    inference(resolution,[],[f297,f179])).
% 1.29/0.55  fof(f179,plain,(
% 1.29/0.55    ~r2_hidden(sK6(u1_struct_0(sK2),sK3),sK3) | spl7_10),
% 1.29/0.55    inference(avatar_component_clause,[],[f177])).
% 1.29/0.55  fof(f177,plain,(
% 1.29/0.55    spl7_10 <=> r2_hidden(sK6(u1_struct_0(sK2),sK3),sK3)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.29/0.55  fof(f297,plain,(
% 1.29/0.55    r2_hidden(sK6(u1_struct_0(sK2),sK3),sK3) | (~spl7_9 | ~spl7_17)),
% 1.29/0.55    inference(resolution,[],[f288,f174])).
% 1.29/0.55  fof(f174,plain,(
% 1.29/0.55    r2_hidden(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~spl7_9),
% 1.29/0.55    inference(avatar_component_clause,[],[f173])).
% 1.29/0.55  fof(f173,plain,(
% 1.29/0.55    spl7_9 <=> r2_hidden(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.29/0.55  fof(f288,plain,(
% 1.29/0.55    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK2)) | r2_hidden(X0,sK3)) ) | ~spl7_17),
% 1.29/0.55    inference(resolution,[],[f263,f73])).
% 1.29/0.55  fof(f263,plain,(
% 1.29/0.55    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r2_hidden(X0,sK3)) ) | ~spl7_17),
% 1.29/0.55    inference(avatar_component_clause,[],[f262])).
% 1.29/0.55  fof(f262,plain,(
% 1.29/0.55    spl7_17 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r2_hidden(X0,sK3))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.29/0.55  fof(f285,plain,(
% 1.29/0.55    spl7_19),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f283])).
% 1.29/0.55  fof(f283,plain,(
% 1.29/0.55    $false | spl7_19),
% 1.29/0.55    inference(resolution,[],[f274,f56])).
% 1.29/0.55  fof(f56,plain,(
% 1.29/0.55    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.29/0.55    inference(cnf_transformation,[],[f36])).
% 1.29/0.55  fof(f274,plain,(
% 1.29/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | spl7_19),
% 1.29/0.55    inference(avatar_component_clause,[],[f272])).
% 1.29/0.55  fof(f272,plain,(
% 1.29/0.55    spl7_19 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.29/0.55  fof(f282,plain,(
% 1.29/0.55    spl7_20),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f280])).
% 1.29/0.55  fof(f280,plain,(
% 1.29/0.55    $false | spl7_20),
% 1.29/0.55    inference(resolution,[],[f278,f55])).
% 1.29/0.55  fof(f55,plain,(
% 1.29/0.55    v13_waybel_0(sK3,sK2)),
% 1.29/0.55    inference(cnf_transformation,[],[f36])).
% 1.29/0.55  fof(f278,plain,(
% 1.29/0.55    ~v13_waybel_0(sK3,sK2) | spl7_20),
% 1.29/0.55    inference(avatar_component_clause,[],[f276])).
% 1.29/0.55  fof(f276,plain,(
% 1.29/0.55    spl7_20 <=> v13_waybel_0(sK3,sK2)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 1.29/0.55  fof(f279,plain,(
% 1.29/0.55    ~spl7_19 | ~spl7_20 | spl7_18),
% 1.29/0.55    inference(avatar_split_clause,[],[f269,f265,f276,f272])).
% 1.29/0.55  fof(f265,plain,(
% 1.29/0.55    spl7_18 <=> sP0(sK3,sK2)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 1.29/0.55  fof(f269,plain,(
% 1.29/0.55    ~v13_waybel_0(sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | spl7_18),
% 1.29/0.55    inference(resolution,[],[f267,f97])).
% 1.29/0.55  fof(f97,plain,(
% 1.29/0.55    ( ! [X1] : (sP0(X1,sK2) | ~v13_waybel_0(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.29/0.55    inference(resolution,[],[f95,f62])).
% 1.29/0.55  fof(f62,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~sP1(X0,X1) | ~v13_waybel_0(X1,X0) | sP0(X1,X0)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f37])).
% 1.29/0.55  fof(f37,plain,(
% 1.29/0.55    ! [X0,X1] : (((v13_waybel_0(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v13_waybel_0(X1,X0))) | ~sP1(X0,X1))),
% 1.29/0.55    inference(nnf_transformation,[],[f30])).
% 1.29/0.55  fof(f30,plain,(
% 1.29/0.55    ! [X0,X1] : ((v13_waybel_0(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 1.29/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.29/0.55  fof(f95,plain,(
% 1.29/0.55    ( ! [X0] : (sP1(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.29/0.55    inference(resolution,[],[f70,f52])).
% 1.29/0.55  fof(f70,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f31])).
% 1.29/0.55  fof(f31,plain,(
% 1.29/0.55    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.29/0.55    inference(definition_folding,[],[f18,f30,f29])).
% 1.29/0.55  fof(f29,plain,(
% 1.29/0.55    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 1.29/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.29/0.55  fof(f18,plain,(
% 1.29/0.55    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.29/0.55    inference(flattening,[],[f17])).
% 1.29/0.55  fof(f17,plain,(
% 1.29/0.55    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.29/0.55    inference(ennf_transformation,[],[f10])).
% 1.29/0.55  fof(f10,axiom,(
% 1.29/0.55    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 1.29/0.55  fof(f267,plain,(
% 1.29/0.55    ~sP0(sK3,sK2) | spl7_18),
% 1.29/0.55    inference(avatar_component_clause,[],[f265])).
% 1.29/0.55  fof(f268,plain,(
% 1.29/0.55    spl7_17 | ~spl7_18 | ~spl7_5 | ~spl7_16),
% 1.29/0.55    inference(avatar_split_clause,[],[f259,f248,f121,f265,f262])).
% 1.29/0.55  fof(f248,plain,(
% 1.29/0.55    spl7_16 <=> ! [X1,X0] : (~r2_hidden(k3_yellow_0(sK2),X0) | ~sP0(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(sK2)) | r2_hidden(X1,X0))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.29/0.55  fof(f259,plain,(
% 1.29/0.55    ( ! [X0] : (~sP0(sK3,sK2) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r2_hidden(X0,sK3)) ) | (~spl7_5 | ~spl7_16)),
% 1.29/0.55    inference(resolution,[],[f249,f128])).
% 1.29/0.55  fof(f128,plain,(
% 1.29/0.55    r2_hidden(k3_yellow_0(sK2),sK3) | ~spl7_5),
% 1.29/0.55    inference(resolution,[],[f123,f92])).
% 1.29/0.55  fof(f92,plain,(
% 1.29/0.55    ( ! [X0] : (~m1_subset_1(X0,sK3) | r2_hidden(X0,sK3)) )),
% 1.29/0.55    inference(resolution,[],[f74,f53])).
% 1.29/0.55  fof(f53,plain,(
% 1.29/0.55    ~v1_xboole_0(sK3)),
% 1.29/0.55    inference(cnf_transformation,[],[f36])).
% 1.29/0.55  fof(f74,plain,(
% 1.29/0.55    ( ! [X0,X1] : (v1_xboole_0(X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f24])).
% 1.29/0.55  fof(f24,plain,(
% 1.29/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.29/0.55    inference(flattening,[],[f23])).
% 1.29/0.55  fof(f23,plain,(
% 1.29/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.29/0.55    inference(ennf_transformation,[],[f6])).
% 1.29/0.55  fof(f6,axiom,(
% 1.29/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.29/0.55  fof(f123,plain,(
% 1.29/0.55    m1_subset_1(k3_yellow_0(sK2),sK3) | ~spl7_5),
% 1.29/0.55    inference(avatar_component_clause,[],[f121])).
% 1.29/0.55  fof(f249,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~r2_hidden(k3_yellow_0(sK2),X0) | ~sP0(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(sK2)) | r2_hidden(X1,X0)) ) | ~spl7_16),
% 1.29/0.55    inference(avatar_component_clause,[],[f248])).
% 1.29/0.55  fof(f258,plain,(
% 1.29/0.55    ~spl7_13),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f257])).
% 1.29/0.55  fof(f257,plain,(
% 1.29/0.55    $false | ~spl7_13),
% 1.29/0.55    inference(resolution,[],[f238,f47])).
% 1.29/0.55  fof(f47,plain,(
% 1.29/0.55    ~v2_struct_0(sK2)),
% 1.29/0.55    inference(cnf_transformation,[],[f36])).
% 1.29/0.55  fof(f238,plain,(
% 1.29/0.55    v2_struct_0(sK2) | ~spl7_13),
% 1.29/0.55    inference(avatar_component_clause,[],[f236])).
% 1.29/0.55  fof(f236,plain,(
% 1.29/0.55    spl7_13 <=> v2_struct_0(sK2)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.29/0.55  fof(f252,plain,(
% 1.29/0.55    spl7_14),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f251])).
% 1.29/0.55  fof(f251,plain,(
% 1.29/0.55    $false | spl7_14),
% 1.29/0.55    inference(resolution,[],[f242,f50])).
% 1.29/0.55  fof(f50,plain,(
% 1.29/0.55    v5_orders_2(sK2)),
% 1.29/0.55    inference(cnf_transformation,[],[f36])).
% 1.29/0.55  fof(f242,plain,(
% 1.29/0.55    ~v5_orders_2(sK2) | spl7_14),
% 1.29/0.55    inference(avatar_component_clause,[],[f240])).
% 1.29/0.55  fof(f240,plain,(
% 1.29/0.55    spl7_14 <=> v5_orders_2(sK2)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.29/0.55  fof(f250,plain,(
% 1.29/0.55    spl7_13 | ~spl7_14 | ~spl7_4 | ~spl7_15 | spl7_16),
% 1.29/0.55    inference(avatar_split_clause,[],[f234,f248,f244,f117,f240,f236])).
% 1.29/0.55  fof(f117,plain,(
% 1.29/0.55    spl7_4 <=> l1_orders_2(sK2)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.29/0.55  fof(f234,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~r2_hidden(k3_yellow_0(sK2),X0) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2)) | ~sP0(X0,sK2) | ~l1_orders_2(sK2) | r2_hidden(X1,X0) | ~v5_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.29/0.55    inference(resolution,[],[f213,f51])).
% 1.29/0.55  fof(f51,plain,(
% 1.29/0.55    v1_yellow_0(sK2)),
% 1.29/0.55    inference(cnf_transformation,[],[f36])).
% 1.29/0.55  fof(f213,plain,(
% 1.29/0.55    ( ! [X4,X5,X3] : (~v1_yellow_0(X5) | ~r2_hidden(k3_yellow_0(X5),X4) | ~m1_subset_1(X3,u1_struct_0(X5)) | ~m1_subset_1(k3_yellow_0(X5),u1_struct_0(X5)) | ~sP0(X4,X5) | ~l1_orders_2(X5) | r2_hidden(X3,X4) | ~v5_orders_2(X5) | v2_struct_0(X5)) )),
% 1.29/0.55    inference(duplicate_literal_removal,[],[f212])).
% 1.29/0.55  fof(f212,plain,(
% 1.29/0.55    ( ! [X4,X5,X3] : (r2_hidden(X3,X4) | ~r2_hidden(k3_yellow_0(X5),X4) | ~m1_subset_1(X3,u1_struct_0(X5)) | ~m1_subset_1(k3_yellow_0(X5),u1_struct_0(X5)) | ~sP0(X4,X5) | ~m1_subset_1(X3,u1_struct_0(X5)) | ~l1_orders_2(X5) | ~v1_yellow_0(X5) | ~v5_orders_2(X5) | v2_struct_0(X5)) )),
% 1.29/0.55    inference(resolution,[],[f64,f72])).
% 1.29/0.55  fof(f72,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f21])).
% 1.29/0.55  fof(f21,plain,(
% 1.29/0.55    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.29/0.55    inference(flattening,[],[f20])).
% 1.29/0.55  fof(f20,plain,(
% 1.29/0.55    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.29/0.55    inference(ennf_transformation,[],[f9])).
% 1.29/0.55  fof(f9,axiom,(
% 1.29/0.55    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).
% 1.29/0.55  fof(f64,plain,(
% 1.29/0.55    ( ! [X4,X0,X5,X1] : (~r1_orders_2(X1,X4,X5) | r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~sP0(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f42])).
% 1.29/0.55  fof(f42,plain,(
% 1.29/0.55    ! [X0,X1] : ((sP0(X0,X1) | ((~r2_hidden(sK5(X0,X1),X0) & r1_orders_2(X1,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X0) & m1_subset_1(sK5(X0,X1),u1_struct_0(X1))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1)))),
% 1.29/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f39,f41,f40])).
% 1.29/0.55  fof(f40,plain,(
% 1.29/0.55    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,X2,X3) & r2_hidden(X2,X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) => (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X1))))),
% 1.29/0.55    introduced(choice_axiom,[])).
% 1.29/0.55  fof(f41,plain,(
% 1.29/0.55    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X0) & m1_subset_1(X3,u1_struct_0(X1))) => (~r2_hidden(sK5(X0,X1),X0) & r1_orders_2(X1,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X0) & m1_subset_1(sK5(X0,X1),u1_struct_0(X1))))),
% 1.29/0.55    introduced(choice_axiom,[])).
% 1.29/0.55  fof(f39,plain,(
% 1.29/0.55    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,X2,X3) & r2_hidden(X2,X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1)))),
% 1.29/0.55    inference(rectify,[],[f38])).
% 1.29/0.55  fof(f38,plain,(
% 1.29/0.55    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~sP0(X1,X0)))),
% 1.29/0.55    inference(nnf_transformation,[],[f29])).
% 1.29/0.55  fof(f208,plain,(
% 1.29/0.55    spl7_9 | ~spl7_10),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f207])).
% 1.29/0.55  fof(f207,plain,(
% 1.29/0.55    $false | (spl7_9 | ~spl7_10)),
% 1.29/0.55    inference(resolution,[],[f205,f194])).
% 1.29/0.55  fof(f194,plain,(
% 1.29/0.55    ~m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | spl7_9),
% 1.29/0.55    inference(resolution,[],[f175,f148])).
% 1.29/0.55  fof(f148,plain,(
% 1.29/0.55    ( ! [X0] : (r2_hidden(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2))) )),
% 1.29/0.55    inference(resolution,[],[f143,f56])).
% 1.29/0.55  fof(f143,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) )),
% 1.29/0.55    inference(resolution,[],[f93,f53])).
% 1.29/0.55  fof(f93,plain,(
% 1.29/0.55    ( ! [X2,X3,X1] : (v1_xboole_0(X3) | ~m1_subset_1(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | r2_hidden(X1,X2)) )),
% 1.29/0.55    inference(resolution,[],[f74,f71])).
% 1.29/0.55  fof(f71,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f19])).
% 1.29/0.55  fof(f19,plain,(
% 1.29/0.55    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.29/0.55    inference(ennf_transformation,[],[f3])).
% 1.29/0.55  fof(f3,axiom,(
% 1.29/0.55    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.29/0.55  fof(f175,plain,(
% 1.29/0.55    ~r2_hidden(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | spl7_9),
% 1.29/0.55    inference(avatar_component_clause,[],[f173])).
% 1.29/0.55  fof(f205,plain,(
% 1.29/0.55    m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~spl7_10),
% 1.29/0.55    inference(resolution,[],[f193,f56])).
% 1.29/0.55  fof(f193,plain,(
% 1.29/0.55    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | m1_subset_1(sK6(u1_struct_0(sK2),sK3),X0)) ) | ~spl7_10),
% 1.29/0.55    inference(resolution,[],[f178,f79])).
% 1.29/0.55  fof(f79,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f28])).
% 1.29/0.55  fof(f28,plain,(
% 1.29/0.55    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.29/0.55    inference(flattening,[],[f27])).
% 1.29/0.55  fof(f27,plain,(
% 1.29/0.55    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.29/0.55    inference(ennf_transformation,[],[f7])).
% 1.29/0.55  fof(f7,axiom,(
% 1.29/0.55    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.29/0.55  fof(f178,plain,(
% 1.29/0.55    r2_hidden(sK6(u1_struct_0(sK2),sK3),sK3) | ~spl7_10),
% 1.29/0.55    inference(avatar_component_clause,[],[f177])).
% 1.29/0.55  fof(f191,plain,(
% 1.29/0.55    spl7_9 | spl7_3 | spl7_10),
% 1.29/0.55    inference(avatar_split_clause,[],[f190,f177,f103,f173])).
% 1.29/0.55  fof(f103,plain,(
% 1.29/0.55    spl7_3 <=> u1_struct_0(sK2) = sK3),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.29/0.55  fof(f190,plain,(
% 1.29/0.55    u1_struct_0(sK2) = sK3 | r2_hidden(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | spl7_10),
% 1.29/0.55    inference(resolution,[],[f179,f77])).
% 1.29/0.55  fof(f77,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | X0 = X1 | r2_hidden(sK6(X0,X1),X0)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f46])).
% 1.29/0.55  fof(f46,plain,(
% 1.29/0.55    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK6(X0,X1),X1) | ~r2_hidden(sK6(X0,X1),X0)) & (r2_hidden(sK6(X0,X1),X1) | r2_hidden(sK6(X0,X1),X0))))),
% 1.29/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).
% 1.29/0.55  fof(f45,plain,(
% 1.29/0.55    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK6(X0,X1),X1) | ~r2_hidden(sK6(X0,X1),X0)) & (r2_hidden(sK6(X0,X1),X1) | r2_hidden(sK6(X0,X1),X0))))),
% 1.29/0.55    introduced(choice_axiom,[])).
% 1.29/0.55  fof(f44,plain,(
% 1.29/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.29/0.55    inference(nnf_transformation,[],[f26])).
% 1.29/0.55  fof(f26,plain,(
% 1.29/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.29/0.55    inference(ennf_transformation,[],[f1])).
% 1.29/0.55  fof(f1,axiom,(
% 1.29/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.29/0.55  fof(f180,plain,(
% 1.29/0.55    ~spl7_9 | ~spl7_10 | spl7_3),
% 1.29/0.55    inference(avatar_split_clause,[],[f167,f103,f177,f173])).
% 1.29/0.55  fof(f167,plain,(
% 1.29/0.55    ~r2_hidden(sK6(u1_struct_0(sK2),sK3),sK3) | ~r2_hidden(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | spl7_3),
% 1.29/0.55    inference(extensionality_resolution,[],[f78,f104])).
% 1.29/0.55  fof(f104,plain,(
% 1.29/0.55    u1_struct_0(sK2) != sK3 | spl7_3),
% 1.29/0.55    inference(avatar_component_clause,[],[f103])).
% 1.29/0.55  fof(f78,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | X0 = X1 | ~r2_hidden(sK6(X0,X1),X0)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f46])).
% 1.29/0.55  fof(f134,plain,(
% 1.29/0.55    ~spl7_1 | ~spl7_3),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f133])).
% 1.29/0.55  fof(f133,plain,(
% 1.29/0.55    $false | (~spl7_1 | ~spl7_3)),
% 1.29/0.55    inference(resolution,[],[f132,f91])).
% 1.29/0.55  fof(f91,plain,(
% 1.29/0.55    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 1.29/0.55    inference(backward_demodulation,[],[f59,f60])).
% 1.29/0.55  fof(f60,plain,(
% 1.29/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.29/0.55    inference(cnf_transformation,[],[f2])).
% 1.29/0.55  fof(f2,axiom,(
% 1.29/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.29/0.55  fof(f59,plain,(
% 1.29/0.55    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f4])).
% 1.29/0.55  fof(f4,axiom,(
% 1.29/0.55    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).
% 1.29/0.55  fof(f132,plain,(
% 1.29/0.55    v1_subset_1(sK3,sK3) | (~spl7_1 | ~spl7_3)),
% 1.29/0.55    inference(forward_demodulation,[],[f83,f105])).
% 1.29/0.55  fof(f105,plain,(
% 1.29/0.55    u1_struct_0(sK2) = sK3 | ~spl7_3),
% 1.29/0.55    inference(avatar_component_clause,[],[f103])).
% 1.29/0.55  fof(f83,plain,(
% 1.29/0.55    v1_subset_1(sK3,u1_struct_0(sK2)) | ~spl7_1),
% 1.29/0.55    inference(avatar_component_clause,[],[f82])).
% 1.29/0.55  fof(f82,plain,(
% 1.29/0.55    spl7_1 <=> v1_subset_1(sK3,u1_struct_0(sK2))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.29/0.55  fof(f131,plain,(
% 1.29/0.55    spl7_2 | ~spl7_5),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f129])).
% 1.29/0.55  fof(f129,plain,(
% 1.29/0.55    $false | (spl7_2 | ~spl7_5)),
% 1.29/0.55    inference(resolution,[],[f128,f87])).
% 1.29/0.55  fof(f87,plain,(
% 1.29/0.55    ~r2_hidden(k3_yellow_0(sK2),sK3) | spl7_2),
% 1.29/0.55    inference(avatar_component_clause,[],[f86])).
% 1.29/0.55  fof(f126,plain,(
% 1.29/0.55    spl7_4),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f125])).
% 1.29/0.55  fof(f125,plain,(
% 1.29/0.55    $false | spl7_4),
% 1.29/0.55    inference(resolution,[],[f119,f52])).
% 1.29/0.55  fof(f119,plain,(
% 1.29/0.55    ~l1_orders_2(sK2) | spl7_4),
% 1.29/0.55    inference(avatar_component_clause,[],[f117])).
% 1.29/0.55  fof(f124,plain,(
% 1.29/0.55    ~spl7_4 | spl7_5 | ~spl7_3),
% 1.29/0.55    inference(avatar_split_clause,[],[f115,f103,f121,f117])).
% 1.29/0.55  fof(f115,plain,(
% 1.29/0.55    m1_subset_1(k3_yellow_0(sK2),sK3) | ~l1_orders_2(sK2) | ~spl7_3),
% 1.29/0.55    inference(superposition,[],[f61,f105])).
% 1.29/0.55  fof(f106,plain,(
% 1.29/0.55    spl7_1 | spl7_3),
% 1.29/0.55    inference(avatar_split_clause,[],[f101,f103,f82])).
% 1.29/0.55  fof(f101,plain,(
% 1.29/0.55    u1_struct_0(sK2) = sK3 | v1_subset_1(sK3,u1_struct_0(sK2))),
% 1.29/0.55    inference(resolution,[],[f76,f56])).
% 1.29/0.55  fof(f76,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f43])).
% 1.29/0.55  fof(f43,plain,(
% 1.29/0.55    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.55    inference(nnf_transformation,[],[f25])).
% 1.29/0.55  fof(f25,plain,(
% 1.29/0.55    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.55    inference(ennf_transformation,[],[f11])).
% 1.29/0.55  fof(f11,axiom,(
% 1.29/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 1.29/0.55  fof(f90,plain,(
% 1.29/0.55    spl7_1 | ~spl7_2),
% 1.29/0.55    inference(avatar_split_clause,[],[f57,f86,f82])).
% 1.29/0.55  fof(f57,plain,(
% 1.29/0.55    ~r2_hidden(k3_yellow_0(sK2),sK3) | v1_subset_1(sK3,u1_struct_0(sK2))),
% 1.29/0.55    inference(cnf_transformation,[],[f36])).
% 1.29/0.55  fof(f89,plain,(
% 1.29/0.55    ~spl7_1 | spl7_2),
% 1.29/0.55    inference(avatar_split_clause,[],[f58,f86,f82])).
% 1.29/0.55  fof(f58,plain,(
% 1.29/0.55    r2_hidden(k3_yellow_0(sK2),sK3) | ~v1_subset_1(sK3,u1_struct_0(sK2))),
% 1.29/0.55    inference(cnf_transformation,[],[f36])).
% 1.29/0.55  % SZS output end Proof for theBenchmark
% 1.29/0.55  % (12712)------------------------------
% 1.29/0.55  % (12712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (12712)Termination reason: Refutation
% 1.29/0.55  
% 1.29/0.55  % (12712)Memory used [KB]: 6396
% 1.29/0.55  % (12712)Time elapsed: 0.111 s
% 1.29/0.55  % (12712)------------------------------
% 1.29/0.55  % (12712)------------------------------
% 1.29/0.55  % (12722)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.29/0.55  % (12699)Success in time 0.179 s
%------------------------------------------------------------------------------
