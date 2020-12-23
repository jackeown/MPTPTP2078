%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:54 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 374 expanded)
%              Number of leaves         :   42 ( 138 expanded)
%              Depth                    :   13
%              Number of atoms          :  736 (2674 expanded)
%              Number of equality atoms :   29 (  48 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f347,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f105,f125,f129,f148,f150,f154,f161,f203,f208,f225,f239,f241,f244,f246,f263,f272,f274,f286,f288,f293,f307,f346])).

fof(f346,plain,
    ( spl7_9
    | ~ spl7_10
    | ~ spl7_23
    | ~ spl7_24 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | spl7_9
    | ~ spl7_10
    | ~ spl7_23
    | ~ spl7_24 ),
    inference(resolution,[],[f324,f195])).

fof(f195,plain,
    ( r2_hidden(sK6(sK3,u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl7_10
  <=> r2_hidden(sK6(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f324,plain,
    ( ~ r2_hidden(sK6(sK3,u1_struct_0(sK2)),u1_struct_0(sK2))
    | spl7_9
    | ~ spl7_23
    | ~ spl7_24 ),
    inference(resolution,[],[f318,f192])).

fof(f192,plain,
    ( ~ r2_hidden(sK6(sK3,u1_struct_0(sK2)),sK3)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl7_9
  <=> r2_hidden(sK6(sK3,u1_struct_0(sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f318,plain,
    ( ! [X4] :
        ( r2_hidden(X4,sK3)
        | ~ r2_hidden(X4,u1_struct_0(sK2)) )
    | ~ spl7_23
    | ~ spl7_24 ),
    inference(resolution,[],[f313,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f313,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r2_hidden(X1,sK3) )
    | ~ spl7_23
    | ~ spl7_24 ),
    inference(duplicate_literal_removal,[],[f310])).

fof(f310,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2)) )
    | ~ spl7_23
    | ~ spl7_24 ),
    inference(resolution,[],[f306,f292])).

fof(f292,plain,
    ( ! [X0] :
        ( r1_orders_2(sK2,k3_yellow_0(sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl7_23
  <=> ! [X0] :
        ( r1_orders_2(sK2,k3_yellow_0(sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f306,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK2,k3_yellow_0(sK2),X0)
        | r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl7_24
  <=> ! [X0] :
        ( ~ r1_orders_2(sK2,k3_yellow_0(sK2),X0)
        | r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f307,plain,
    ( ~ spl7_5
    | ~ spl7_2
    | spl7_24
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f299,f261,f305,f101,f141])).

fof(f141,plain,
    ( spl7_5
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f101,plain,
    ( spl7_2
  <=> r2_hidden(k3_yellow_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f261,plain,
    ( spl7_18
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ r1_orders_2(sK2,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r2_hidden(X1,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK2,k3_yellow_0(sK2),X0)
        | ~ r2_hidden(k3_yellow_0(sK2),sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r2_hidden(X0,sK3)
        | ~ l1_orders_2(sK2) )
    | ~ spl7_18 ),
    inference(resolution,[],[f262,f71])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f262,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_orders_2(sK2,X0,X1)
        | ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r2_hidden(X1,sK3) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f261])).

fof(f293,plain,
    ( ~ spl7_5
    | spl7_23
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f289,f284,f291,f141])).

fof(f284,plain,
    ( spl7_22
  <=> ! [X0] :
        ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f289,plain,
    ( ! [X0] :
        ( r1_orders_2(sK2,k3_yellow_0(sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ l1_orders_2(sK2) )
    | ~ spl7_22 ),
    inference(superposition,[],[f285,f72])).

fof(f72,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f285,plain,
    ( ! [X0] :
        ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f284])).

fof(f288,plain,(
    spl7_21 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | spl7_21 ),
    inference(resolution,[],[f282,f58])).

fof(f58,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f44,f43])).

fof(f43,plain,
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

fof(f44,plain,
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

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f17])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f282,plain,
    ( ~ v4_orders_2(sK2)
    | spl7_21 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl7_21
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f286,plain,
    ( spl7_13
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_14
    | ~ spl7_5
    | spl7_22
    | ~ spl7_11
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f278,f270,f219,f284,f141,f232,f280,f266,f228])).

fof(f228,plain,
    ( spl7_13
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f266,plain,
    ( spl7_19
  <=> v3_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f232,plain,
    ( spl7_14
  <=> v5_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f219,plain,
    ( spl7_11
  <=> ! [X0] :
        ( ~ r1_yellow_0(sK2,X0)
        | r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),k1_yellow_0(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f270,plain,
    ( spl7_20
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | k1_yellow_0(sK2,k5_waybel_0(sK2,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f278,plain,
    ( ! [X0] :
        ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | ~ v5_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl7_11
    | ~ spl7_20 ),
    inference(duplicate_literal_removal,[],[f277])).

fof(f277,plain,
    ( ! [X0] :
        ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | ~ v5_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl7_11
    | ~ spl7_20 ),
    inference(resolution,[],[f276,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_waybel_0)).

fof(f276,plain,
    ( ! [X1] :
        ( ~ r1_yellow_0(sK2,k5_waybel_0(sK2,X1))
        | r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2)) )
    | ~ spl7_11
    | ~ spl7_20 ),
    inference(superposition,[],[f220,f271])).

fof(f271,plain,
    ( ! [X0] :
        ( k1_yellow_0(sK2,k5_waybel_0(sK2,X0)) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f270])).

fof(f220,plain,
    ( ! [X0] :
        ( r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),k1_yellow_0(sK2,X0))
        | ~ r1_yellow_0(sK2,X0) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f219])).

fof(f274,plain,(
    spl7_19 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | spl7_19 ),
    inference(resolution,[],[f268,f57])).

fof(f57,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f268,plain,
    ( ~ v3_orders_2(sK2)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f266])).

fof(f272,plain,
    ( spl7_13
    | ~ spl7_19
    | ~ spl7_14
    | ~ spl7_5
    | spl7_20 ),
    inference(avatar_split_clause,[],[f264,f270,f141,f232,f266,f228])).

fof(f264,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ v5_orders_2(sK2)
      | k1_yellow_0(sK2,k5_waybel_0(sK2,X0)) = X0
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f84,f58])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f263,plain,
    ( ~ spl7_3
    | spl7_18 ),
    inference(avatar_split_clause,[],[f259,f261,f118])).

fof(f118,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f259,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r2_hidden(X1,sK3)
      | ~ r1_orders_2(sK2,X0,X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f242,f64])).

fof(f64,plain,(
    v13_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f242,plain,(
    ! [X2,X0,X1] :
      ( ~ v13_waybel_0(X2,sK2)
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r2_hidden(X1,X2)
      | ~ r1_orders_2(sK2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f75,f111])).

fof(f111,plain,(
    ! [X1] :
      ( sP0(X1,sK2)
      | ~ v13_waybel_0(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f109,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v13_waybel_0(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v13_waybel_0(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f109,plain,(
    ! [X0] :
      ( sP1(sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f81,f61])).

fof(f61,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f23,f39,f38])).

fof(f38,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f75,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r2_hidden(X5,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f48,f50,f49])).

fof(f49,plain,(
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

fof(f50,plain,(
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

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f246,plain,(
    ~ spl7_13 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | ~ spl7_13 ),
    inference(resolution,[],[f230,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f230,plain,
    ( v2_struct_0(sK2)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f228])).

fof(f244,plain,(
    spl7_15 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | spl7_15 ),
    inference(resolution,[],[f238,f60])).

fof(f60,plain,(
    v1_yellow_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f238,plain,
    ( ~ v1_yellow_0(sK2)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl7_15
  <=> v1_yellow_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f241,plain,(
    spl7_14 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl7_14 ),
    inference(resolution,[],[f234,f59])).

fof(f59,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f234,plain,
    ( ~ v5_orders_2(sK2)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f232])).

fof(f239,plain,
    ( spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_5
    | spl7_12 ),
    inference(avatar_split_clause,[],[f226,f222,f141,f236,f232,f228])).

fof(f222,plain,
    ( spl7_12
  <=> r1_yellow_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f226,plain,
    ( ~ l1_orders_2(sK2)
    | ~ v1_yellow_0(sK2)
    | ~ v5_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl7_12 ),
    inference(resolution,[],[f224,f85])).

fof(f85,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f224,plain,
    ( ~ r1_yellow_0(sK2,k1_xboole_0)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f222])).

fof(f225,plain,
    ( spl7_11
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f217,f222,f219])).

fof(f217,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK2,k1_xboole_0)
      | ~ r1_yellow_0(sK2,X0)
      | r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),k1_yellow_0(sK2,X0)) ) ),
    inference(resolution,[],[f201,f68])).

fof(f68,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_yellow_0(sK2,X1)
      | ~ r1_yellow_0(sK2,X0)
      | r1_orders_2(sK2,k1_yellow_0(sK2,X1),k1_yellow_0(sK2,X0)) ) ),
    inference(resolution,[],[f82,f61])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_yellow_0)).

fof(f208,plain,
    ( ~ spl7_9
    | spl7_4
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f205,f190,f118,f122,f190])).

fof(f122,plain,
    ( spl7_4
  <=> u1_struct_0(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f205,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK2) = sK3
    | ~ r2_hidden(sK6(sK3,u1_struct_0(sK2)),sK3)
    | ~ spl7_9 ),
    inference(resolution,[],[f204,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | X0 = X1
      | ~ r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK6(X0,X1),X1)
          | ~ r2_hidden(sK6(X0,X1),X0) )
        & ( r2_hidden(sK6(X0,X1),X1)
          | r2_hidden(sK6(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f53,f54])).

fof(f54,plain,(
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

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f204,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(sK3,u1_struct_0(sK2)),X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) )
    | ~ spl7_9 ),
    inference(resolution,[],[f191,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f191,plain,
    ( r2_hidden(sK6(sK3,u1_struct_0(sK2)),sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f190])).

fof(f203,plain,
    ( spl7_9
    | spl7_4
    | spl7_10 ),
    inference(avatar_split_clause,[],[f202,f194,f122,f190])).

fof(f202,plain,
    ( u1_struct_0(sK2) = sK3
    | r2_hidden(sK6(sK3,u1_struct_0(sK2)),sK3)
    | spl7_10 ),
    inference(resolution,[],[f196,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f196,plain,
    ( ~ r2_hidden(sK6(sK3,u1_struct_0(sK2)),u1_struct_0(sK2))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f194])).

fof(f161,plain,
    ( ~ spl7_1
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(resolution,[],[f156,f106])).

fof(f106,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f70,f69])).

fof(f69,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f156,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(resolution,[],[f155,f95])).

fof(f95,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f155,plain,
    ( v1_subset_1(sK3,sK3)
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f98,f124])).

fof(f124,plain,
    ( u1_struct_0(sK2) = sK3
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f98,plain,
    ( v1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl7_1
  <=> v1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f154,plain,
    ( spl7_2
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f151,f102])).

fof(f102,plain,
    ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f151,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f147,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK3)
      | r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f88,f62])).

fof(f62,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f147,plain,
    ( m1_subset_1(k3_yellow_0(sK2),sK3)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl7_6
  <=> m1_subset_1(k3_yellow_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f150,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl7_5 ),
    inference(resolution,[],[f143,f61])).

fof(f143,plain,
    ( ~ l1_orders_2(sK2)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f141])).

fof(f148,plain,
    ( ~ spl7_5
    | spl7_6
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f139,f122,f145,f141])).

fof(f139,plain,
    ( m1_subset_1(k3_yellow_0(sK2),sK3)
    | ~ l1_orders_2(sK2)
    | ~ spl7_4 ),
    inference(superposition,[],[f71,f124])).

fof(f129,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl7_3 ),
    inference(resolution,[],[f120,f65])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f120,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f125,plain,
    ( ~ spl7_3
    | spl7_4
    | spl7_1 ),
    inference(avatar_split_clause,[],[f114,f97,f122,f118])).

fof(f114,plain,
    ( u1_struct_0(sK2) = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_1 ),
    inference(resolution,[],[f90,f99])).

fof(f99,plain,
    ( ~ v1_subset_1(sK3,u1_struct_0(sK2))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f105,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f66,f101,f97])).

fof(f66,plain,
    ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f104,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f67,f101,f97])).

fof(f67,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:18:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (21071)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (21063)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (21055)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.19/0.51  % (21050)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.19/0.53  % (21052)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.53  % (21051)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.54  % (21053)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.54  % (21060)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.54  % (21048)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.54  % (21050)Refutation not found, incomplete strategy% (21050)------------------------------
% 1.29/0.54  % (21050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (21050)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (21050)Memory used [KB]: 11001
% 1.29/0.54  % (21050)Time elapsed: 0.120 s
% 1.29/0.54  % (21050)------------------------------
% 1.29/0.54  % (21050)------------------------------
% 1.29/0.54  % (21068)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.29/0.54  % (21069)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.29/0.54  % (21067)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.54  % (21074)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.54  % (21065)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.29/0.55  % (21074)Refutation not found, incomplete strategy% (21074)------------------------------
% 1.29/0.55  % (21074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (21074)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (21074)Memory used [KB]: 10746
% 1.29/0.55  % (21074)Time elapsed: 0.130 s
% 1.29/0.55  % (21074)------------------------------
% 1.29/0.55  % (21074)------------------------------
% 1.29/0.55  % (21065)Refutation not found, incomplete strategy% (21065)------------------------------
% 1.29/0.55  % (21065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (21065)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (21065)Memory used [KB]: 10746
% 1.29/0.55  % (21065)Time elapsed: 0.129 s
% 1.29/0.55  % (21065)------------------------------
% 1.29/0.55  % (21065)------------------------------
% 1.29/0.55  % (21072)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.55  % (21075)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.55  % (21077)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.55  % (21066)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.55  % (21057)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.55  % (21054)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.55  % (21052)Refutation not found, incomplete strategy% (21052)------------------------------
% 1.29/0.55  % (21052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (21052)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (21052)Memory used [KB]: 6268
% 1.29/0.55  % (21052)Time elapsed: 0.138 s
% 1.29/0.55  % (21052)------------------------------
% 1.29/0.55  % (21052)------------------------------
% 1.29/0.55  % (21076)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.29/0.55  % (21059)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.29/0.55  % (21056)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.55  % (21058)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.29/0.56  % (21061)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.56  % (21073)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.56  % (21049)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.56  % (21056)Refutation not found, incomplete strategy% (21056)------------------------------
% 1.29/0.56  % (21056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (21056)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.56  
% 1.29/0.56  % (21056)Memory used [KB]: 10746
% 1.29/0.56  % (21056)Time elapsed: 0.141 s
% 1.29/0.56  % (21056)------------------------------
% 1.29/0.56  % (21056)------------------------------
% 1.29/0.56  % (21064)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.56  % (21060)Refutation found. Thanks to Tanya!
% 1.29/0.56  % SZS status Theorem for theBenchmark
% 1.29/0.56  % SZS output start Proof for theBenchmark
% 1.29/0.56  fof(f347,plain,(
% 1.29/0.56    $false),
% 1.29/0.56    inference(avatar_sat_refutation,[],[f104,f105,f125,f129,f148,f150,f154,f161,f203,f208,f225,f239,f241,f244,f246,f263,f272,f274,f286,f288,f293,f307,f346])).
% 1.29/0.56  fof(f346,plain,(
% 1.29/0.56    spl7_9 | ~spl7_10 | ~spl7_23 | ~spl7_24),
% 1.29/0.56    inference(avatar_contradiction_clause,[],[f344])).
% 1.29/0.56  fof(f344,plain,(
% 1.29/0.56    $false | (spl7_9 | ~spl7_10 | ~spl7_23 | ~spl7_24)),
% 1.29/0.56    inference(resolution,[],[f324,f195])).
% 1.29/0.56  fof(f195,plain,(
% 1.29/0.56    r2_hidden(sK6(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)) | ~spl7_10),
% 1.29/0.56    inference(avatar_component_clause,[],[f194])).
% 1.29/0.56  fof(f194,plain,(
% 1.29/0.56    spl7_10 <=> r2_hidden(sK6(sK3,u1_struct_0(sK2)),u1_struct_0(sK2))),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.29/0.56  fof(f324,plain,(
% 1.29/0.56    ~r2_hidden(sK6(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)) | (spl7_9 | ~spl7_23 | ~spl7_24)),
% 1.29/0.56    inference(resolution,[],[f318,f192])).
% 1.29/0.56  fof(f192,plain,(
% 1.29/0.56    ~r2_hidden(sK6(sK3,u1_struct_0(sK2)),sK3) | spl7_9),
% 1.29/0.56    inference(avatar_component_clause,[],[f190])).
% 1.29/0.56  fof(f190,plain,(
% 1.29/0.56    spl7_9 <=> r2_hidden(sK6(sK3,u1_struct_0(sK2)),sK3)),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.29/0.56  fof(f318,plain,(
% 1.29/0.56    ( ! [X4] : (r2_hidden(X4,sK3) | ~r2_hidden(X4,u1_struct_0(sK2))) ) | (~spl7_23 | ~spl7_24)),
% 1.29/0.56    inference(resolution,[],[f313,f87])).
% 1.29/0.56  fof(f87,plain,(
% 1.29/0.56    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f30])).
% 1.29/0.56  fof(f30,plain,(
% 1.29/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.29/0.56    inference(ennf_transformation,[],[f6])).
% 1.29/0.56  fof(f6,axiom,(
% 1.29/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.29/0.56  fof(f313,plain,(
% 1.29/0.56    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK2)) | r2_hidden(X1,sK3)) ) | (~spl7_23 | ~spl7_24)),
% 1.29/0.56    inference(duplicate_literal_removal,[],[f310])).
% 1.29/0.56  fof(f310,plain,(
% 1.29/0.56    ( ! [X1] : (r2_hidden(X1,sK3) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2))) ) | (~spl7_23 | ~spl7_24)),
% 1.29/0.56    inference(resolution,[],[f306,f292])).
% 1.29/0.56  fof(f292,plain,(
% 1.29/0.56    ( ! [X0] : (r1_orders_2(sK2,k3_yellow_0(sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK2))) ) | ~spl7_23),
% 1.29/0.56    inference(avatar_component_clause,[],[f291])).
% 1.29/0.56  fof(f291,plain,(
% 1.29/0.56    spl7_23 <=> ! [X0] : (r1_orders_2(sK2,k3_yellow_0(sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK2)))),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 1.29/0.56  fof(f306,plain,(
% 1.29/0.56    ( ! [X0] : (~r1_orders_2(sK2,k3_yellow_0(sK2),X0) | r2_hidden(X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK2))) ) | ~spl7_24),
% 1.29/0.56    inference(avatar_component_clause,[],[f305])).
% 1.29/0.56  fof(f305,plain,(
% 1.29/0.56    spl7_24 <=> ! [X0] : (~r1_orders_2(sK2,k3_yellow_0(sK2),X0) | r2_hidden(X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK2)))),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 1.29/0.56  fof(f307,plain,(
% 1.29/0.56    ~spl7_5 | ~spl7_2 | spl7_24 | ~spl7_18),
% 1.29/0.56    inference(avatar_split_clause,[],[f299,f261,f305,f101,f141])).
% 1.29/0.56  fof(f141,plain,(
% 1.29/0.56    spl7_5 <=> l1_orders_2(sK2)),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.29/0.56  fof(f101,plain,(
% 1.29/0.56    spl7_2 <=> r2_hidden(k3_yellow_0(sK2),sK3)),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.29/0.56  fof(f261,plain,(
% 1.29/0.56    spl7_18 <=> ! [X1,X0] : (~r2_hidden(X0,sK3) | ~r1_orders_2(sK2,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | r2_hidden(X1,sK3))),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 1.29/0.56  fof(f299,plain,(
% 1.29/0.56    ( ! [X0] : (~r1_orders_2(sK2,k3_yellow_0(sK2),X0) | ~r2_hidden(k3_yellow_0(sK2),sK3) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r2_hidden(X0,sK3) | ~l1_orders_2(sK2)) ) | ~spl7_18),
% 1.29/0.56    inference(resolution,[],[f262,f71])).
% 1.29/0.56  fof(f71,plain,(
% 1.29/0.56    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f20])).
% 1.29/0.56  fof(f20,plain,(
% 1.29/0.56    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.29/0.56    inference(ennf_transformation,[],[f10])).
% 1.29/0.56  fof(f10,axiom,(
% 1.29/0.56    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 1.29/0.56  fof(f262,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_orders_2(sK2,X0,X1) | ~r2_hidden(X0,sK3) | ~m1_subset_1(X1,u1_struct_0(sK2)) | r2_hidden(X1,sK3)) ) | ~spl7_18),
% 1.29/0.56    inference(avatar_component_clause,[],[f261])).
% 1.29/0.56  fof(f293,plain,(
% 1.29/0.56    ~spl7_5 | spl7_23 | ~spl7_22),
% 1.29/0.56    inference(avatar_split_clause,[],[f289,f284,f291,f141])).
% 1.29/0.56  fof(f284,plain,(
% 1.29/0.56    spl7_22 <=> ! [X0] : (r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK2)))),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 1.29/0.56  fof(f289,plain,(
% 1.29/0.56    ( ! [X0] : (r1_orders_2(sK2,k3_yellow_0(sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_orders_2(sK2)) ) | ~spl7_22),
% 1.29/0.56    inference(superposition,[],[f285,f72])).
% 1.29/0.56  fof(f72,plain,(
% 1.29/0.56    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f21])).
% 1.29/0.56  fof(f21,plain,(
% 1.29/0.56    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 1.29/0.56    inference(ennf_transformation,[],[f9])).
% 1.29/0.56  fof(f9,axiom,(
% 1.29/0.56    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).
% 1.29/0.56  fof(f285,plain,(
% 1.29/0.56    ( ! [X0] : (r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK2))) ) | ~spl7_22),
% 1.29/0.56    inference(avatar_component_clause,[],[f284])).
% 1.29/0.56  fof(f288,plain,(
% 1.29/0.56    spl7_21),
% 1.29/0.56    inference(avatar_contradiction_clause,[],[f287])).
% 1.29/0.56  fof(f287,plain,(
% 1.29/0.56    $false | spl7_21),
% 1.29/0.56    inference(resolution,[],[f282,f58])).
% 1.29/0.56  fof(f58,plain,(
% 1.29/0.56    v4_orders_2(sK2)),
% 1.29/0.56    inference(cnf_transformation,[],[f45])).
% 1.29/0.56  fof(f45,plain,(
% 1.29/0.56    ((r2_hidden(k3_yellow_0(sK2),sK3) | ~v1_subset_1(sK3,u1_struct_0(sK2))) & (~r2_hidden(k3_yellow_0(sK2),sK3) | v1_subset_1(sK3,u1_struct_0(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v13_waybel_0(sK3,sK2) & v2_waybel_0(sK3,sK2) & ~v1_xboole_0(sK3)) & l1_orders_2(sK2) & v1_yellow_0(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 1.29/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f44,f43])).
% 1.29/0.56  fof(f43,plain,(
% 1.29/0.56    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK2),X1) | ~v1_subset_1(X1,u1_struct_0(sK2))) & (~r2_hidden(k3_yellow_0(sK2),X1) | v1_subset_1(X1,u1_struct_0(sK2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v13_waybel_0(X1,sK2) & v2_waybel_0(X1,sK2) & ~v1_xboole_0(X1)) & l1_orders_2(sK2) & v1_yellow_0(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f44,plain,(
% 1.29/0.56    ? [X1] : ((r2_hidden(k3_yellow_0(sK2),X1) | ~v1_subset_1(X1,u1_struct_0(sK2))) & (~r2_hidden(k3_yellow_0(sK2),X1) | v1_subset_1(X1,u1_struct_0(sK2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v13_waybel_0(X1,sK2) & v2_waybel_0(X1,sK2) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK2),sK3) | ~v1_subset_1(sK3,u1_struct_0(sK2))) & (~r2_hidden(k3_yellow_0(sK2),sK3) | v1_subset_1(sK3,u1_struct_0(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v13_waybel_0(sK3,sK2) & v2_waybel_0(sK3,sK2) & ~v1_xboole_0(sK3))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f42,plain,(
% 1.29/0.56    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.29/0.56    inference(flattening,[],[f41])).
% 1.29/0.56  fof(f41,plain,(
% 1.29/0.56    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.29/0.56    inference(nnf_transformation,[],[f19])).
% 1.29/0.56  fof(f19,plain,(
% 1.29/0.56    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.29/0.56    inference(flattening,[],[f18])).
% 1.29/0.56  fof(f18,plain,(
% 1.29/0.56    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f17])).
% 1.29/0.56  fof(f17,negated_conjecture,(
% 1.29/0.56    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.29/0.56    inference(negated_conjecture,[],[f16])).
% 1.29/0.56  fof(f16,conjecture,(
% 1.29/0.56    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).
% 1.29/0.56  fof(f282,plain,(
% 1.29/0.56    ~v4_orders_2(sK2) | spl7_21),
% 1.29/0.56    inference(avatar_component_clause,[],[f280])).
% 1.29/0.56  fof(f280,plain,(
% 1.29/0.56    spl7_21 <=> v4_orders_2(sK2)),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 1.29/0.56  fof(f286,plain,(
% 1.29/0.56    spl7_13 | ~spl7_19 | ~spl7_21 | ~spl7_14 | ~spl7_5 | spl7_22 | ~spl7_11 | ~spl7_20),
% 1.29/0.56    inference(avatar_split_clause,[],[f278,f270,f219,f284,f141,f232,f280,f266,f228])).
% 1.29/0.56  fof(f228,plain,(
% 1.29/0.56    spl7_13 <=> v2_struct_0(sK2)),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.29/0.56  fof(f266,plain,(
% 1.29/0.56    spl7_19 <=> v3_orders_2(sK2)),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.29/0.56  fof(f232,plain,(
% 1.29/0.56    spl7_14 <=> v5_orders_2(sK2)),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.29/0.56  fof(f219,plain,(
% 1.29/0.56    spl7_11 <=> ! [X0] : (~r1_yellow_0(sK2,X0) | r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),k1_yellow_0(sK2,X0)))),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.29/0.56  fof(f270,plain,(
% 1.29/0.56    spl7_20 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | k1_yellow_0(sK2,k5_waybel_0(sK2,X0)) = X0)),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 1.29/0.56  fof(f278,plain,(
% 1.29/0.56    ( ! [X0] : (r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) ) | (~spl7_11 | ~spl7_20)),
% 1.29/0.56    inference(duplicate_literal_removal,[],[f277])).
% 1.29/0.56  fof(f277,plain,(
% 1.29/0.56    ( ! [X0] : (r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) ) | (~spl7_11 | ~spl7_20)),
% 1.29/0.56    inference(resolution,[],[f276,f83])).
% 1.29/0.56  fof(f83,plain,(
% 1.29/0.56    ( ! [X0,X1] : (r1_yellow_0(X0,k5_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f27])).
% 1.29/0.56  fof(f27,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.29/0.56    inference(flattening,[],[f26])).
% 1.29/0.56  fof(f26,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f14])).
% 1.29/0.56  fof(f14,axiom,(
% 1.29/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1)))))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_waybel_0)).
% 1.29/0.56  fof(f276,plain,(
% 1.29/0.56    ( ! [X1] : (~r1_yellow_0(sK2,k5_waybel_0(sK2,X1)) | r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),X1) | ~m1_subset_1(X1,u1_struct_0(sK2))) ) | (~spl7_11 | ~spl7_20)),
% 1.29/0.56    inference(superposition,[],[f220,f271])).
% 1.29/0.56  fof(f271,plain,(
% 1.29/0.56    ( ! [X0] : (k1_yellow_0(sK2,k5_waybel_0(sK2,X0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK2))) ) | ~spl7_20),
% 1.29/0.56    inference(avatar_component_clause,[],[f270])).
% 1.29/0.56  fof(f220,plain,(
% 1.29/0.56    ( ! [X0] : (r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),k1_yellow_0(sK2,X0)) | ~r1_yellow_0(sK2,X0)) ) | ~spl7_11),
% 1.29/0.56    inference(avatar_component_clause,[],[f219])).
% 1.29/0.56  fof(f274,plain,(
% 1.29/0.56    spl7_19),
% 1.29/0.56    inference(avatar_contradiction_clause,[],[f273])).
% 1.29/0.56  fof(f273,plain,(
% 1.29/0.56    $false | spl7_19),
% 1.29/0.56    inference(resolution,[],[f268,f57])).
% 1.29/0.56  fof(f57,plain,(
% 1.29/0.56    v3_orders_2(sK2)),
% 1.29/0.56    inference(cnf_transformation,[],[f45])).
% 1.29/0.56  fof(f268,plain,(
% 1.29/0.56    ~v3_orders_2(sK2) | spl7_19),
% 1.29/0.56    inference(avatar_component_clause,[],[f266])).
% 1.29/0.56  fof(f272,plain,(
% 1.29/0.56    spl7_13 | ~spl7_19 | ~spl7_14 | ~spl7_5 | spl7_20),
% 1.29/0.56    inference(avatar_split_clause,[],[f264,f270,f141,f232,f266,f228])).
% 1.29/0.56  fof(f264,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~v5_orders_2(sK2) | k1_yellow_0(sK2,k5_waybel_0(sK2,X0)) = X0 | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.29/0.56    inference(resolution,[],[f84,f58])).
% 1.29/0.56  fof(f84,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~v4_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f27])).
% 1.29/0.56  fof(f263,plain,(
% 1.29/0.56    ~spl7_3 | spl7_18),
% 1.29/0.56    inference(avatar_split_clause,[],[f259,f261,f118])).
% 1.29/0.56  fof(f118,plain,(
% 1.29/0.56    spl7_3 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.29/0.56  fof(f259,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK3) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r2_hidden(X1,sK3) | ~r1_orders_2(sK2,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.29/0.56    inference(resolution,[],[f242,f64])).
% 1.29/0.56  fof(f64,plain,(
% 1.29/0.56    v13_waybel_0(sK3,sK2)),
% 1.29/0.56    inference(cnf_transformation,[],[f45])).
% 1.29/0.56  fof(f242,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (~v13_waybel_0(X2,sK2) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r2_hidden(X1,X2) | ~r1_orders_2(sK2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.29/0.56    inference(resolution,[],[f75,f111])).
% 1.29/0.56  fof(f111,plain,(
% 1.29/0.56    ( ! [X1] : (sP0(X1,sK2) | ~v13_waybel_0(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.29/0.56    inference(resolution,[],[f109,f73])).
% 1.29/0.56  fof(f73,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~sP1(X0,X1) | ~v13_waybel_0(X1,X0) | sP0(X1,X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f46])).
% 1.29/0.56  fof(f46,plain,(
% 1.29/0.56    ! [X0,X1] : (((v13_waybel_0(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v13_waybel_0(X1,X0))) | ~sP1(X0,X1))),
% 1.29/0.56    inference(nnf_transformation,[],[f39])).
% 1.29/0.56  fof(f39,plain,(
% 1.29/0.56    ! [X0,X1] : ((v13_waybel_0(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 1.29/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.29/0.56  fof(f109,plain,(
% 1.29/0.56    ( ! [X0] : (sP1(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.29/0.56    inference(resolution,[],[f81,f61])).
% 1.29/0.56  fof(f61,plain,(
% 1.29/0.56    l1_orders_2(sK2)),
% 1.29/0.56    inference(cnf_transformation,[],[f45])).
% 1.29/0.56  fof(f81,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f40])).
% 1.29/0.56  fof(f40,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.29/0.56    inference(definition_folding,[],[f23,f39,f38])).
% 1.29/0.56  fof(f38,plain,(
% 1.29/0.56    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 1.29/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.29/0.56  fof(f23,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.29/0.56    inference(flattening,[],[f22])).
% 1.29/0.56  fof(f22,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.29/0.56    inference(ennf_transformation,[],[f13])).
% 1.29/0.56  fof(f13,axiom,(
% 1.29/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).
% 1.29/0.56  fof(f75,plain,(
% 1.29/0.56    ( ! [X4,X0,X5,X1] : (~sP0(X0,X1) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | r2_hidden(X5,X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f51])).
% 1.29/0.56  fof(f51,plain,(
% 1.29/0.56    ! [X0,X1] : ((sP0(X0,X1) | ((~r2_hidden(sK5(X0,X1),X0) & r1_orders_2(X1,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X0) & m1_subset_1(sK5(X0,X1),u1_struct_0(X1))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1)))),
% 1.29/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f48,f50,f49])).
% 1.29/0.56  fof(f49,plain,(
% 1.29/0.56    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,X2,X3) & r2_hidden(X2,X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) => (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X1))))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f50,plain,(
% 1.29/0.56    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X0) & m1_subset_1(X3,u1_struct_0(X1))) => (~r2_hidden(sK5(X0,X1),X0) & r1_orders_2(X1,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X0) & m1_subset_1(sK5(X0,X1),u1_struct_0(X1))))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f48,plain,(
% 1.29/0.56    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,X2,X3) & r2_hidden(X2,X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1)))),
% 1.29/0.56    inference(rectify,[],[f47])).
% 1.29/0.56  fof(f47,plain,(
% 1.29/0.56    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~sP0(X1,X0)))),
% 1.29/0.56    inference(nnf_transformation,[],[f38])).
% 1.29/0.56  fof(f246,plain,(
% 1.29/0.56    ~spl7_13),
% 1.29/0.56    inference(avatar_contradiction_clause,[],[f245])).
% 1.29/0.56  fof(f245,plain,(
% 1.29/0.56    $false | ~spl7_13),
% 1.29/0.56    inference(resolution,[],[f230,f56])).
% 1.29/0.56  fof(f56,plain,(
% 1.29/0.56    ~v2_struct_0(sK2)),
% 1.29/0.56    inference(cnf_transformation,[],[f45])).
% 1.29/0.56  fof(f230,plain,(
% 1.29/0.56    v2_struct_0(sK2) | ~spl7_13),
% 1.29/0.56    inference(avatar_component_clause,[],[f228])).
% 1.29/0.56  fof(f244,plain,(
% 1.29/0.56    spl7_15),
% 1.29/0.56    inference(avatar_contradiction_clause,[],[f243])).
% 1.29/0.56  fof(f243,plain,(
% 1.29/0.56    $false | spl7_15),
% 1.29/0.56    inference(resolution,[],[f238,f60])).
% 1.29/0.56  fof(f60,plain,(
% 1.29/0.56    v1_yellow_0(sK2)),
% 1.29/0.56    inference(cnf_transformation,[],[f45])).
% 1.29/0.56  fof(f238,plain,(
% 1.29/0.56    ~v1_yellow_0(sK2) | spl7_15),
% 1.29/0.56    inference(avatar_component_clause,[],[f236])).
% 1.29/0.56  fof(f236,plain,(
% 1.29/0.56    spl7_15 <=> v1_yellow_0(sK2)),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.29/0.56  fof(f241,plain,(
% 1.29/0.56    spl7_14),
% 1.29/0.56    inference(avatar_contradiction_clause,[],[f240])).
% 1.29/0.56  fof(f240,plain,(
% 1.29/0.56    $false | spl7_14),
% 1.29/0.56    inference(resolution,[],[f234,f59])).
% 1.29/0.56  fof(f59,plain,(
% 1.29/0.56    v5_orders_2(sK2)),
% 1.29/0.56    inference(cnf_transformation,[],[f45])).
% 1.29/0.56  fof(f234,plain,(
% 1.29/0.56    ~v5_orders_2(sK2) | spl7_14),
% 1.29/0.56    inference(avatar_component_clause,[],[f232])).
% 1.29/0.56  fof(f239,plain,(
% 1.29/0.56    spl7_13 | ~spl7_14 | ~spl7_15 | ~spl7_5 | spl7_12),
% 1.29/0.56    inference(avatar_split_clause,[],[f226,f222,f141,f236,f232,f228])).
% 1.29/0.56  fof(f222,plain,(
% 1.29/0.56    spl7_12 <=> r1_yellow_0(sK2,k1_xboole_0)),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.29/0.56  fof(f226,plain,(
% 1.29/0.56    ~l1_orders_2(sK2) | ~v1_yellow_0(sK2) | ~v5_orders_2(sK2) | v2_struct_0(sK2) | spl7_12),
% 1.29/0.56    inference(resolution,[],[f224,f85])).
% 1.29/0.56  fof(f85,plain,(
% 1.29/0.56    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f29])).
% 1.29/0.56  fof(f29,plain,(
% 1.29/0.56    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.29/0.56    inference(flattening,[],[f28])).
% 1.29/0.56  fof(f28,plain,(
% 1.29/0.56    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f12])).
% 1.29/0.56  fof(f12,axiom,(
% 1.29/0.56    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).
% 1.29/0.56  fof(f224,plain,(
% 1.29/0.56    ~r1_yellow_0(sK2,k1_xboole_0) | spl7_12),
% 1.29/0.56    inference(avatar_component_clause,[],[f222])).
% 1.29/0.56  fof(f225,plain,(
% 1.29/0.56    spl7_11 | ~spl7_12),
% 1.29/0.56    inference(avatar_split_clause,[],[f217,f222,f219])).
% 1.29/0.56  fof(f217,plain,(
% 1.29/0.56    ( ! [X0] : (~r1_yellow_0(sK2,k1_xboole_0) | ~r1_yellow_0(sK2,X0) | r1_orders_2(sK2,k1_yellow_0(sK2,k1_xboole_0),k1_yellow_0(sK2,X0))) )),
% 1.29/0.56    inference(resolution,[],[f201,f68])).
% 1.29/0.56  fof(f68,plain,(
% 1.29/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f2])).
% 1.29/0.56  fof(f2,axiom,(
% 1.29/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.29/0.56  fof(f201,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_yellow_0(sK2,X1) | ~r1_yellow_0(sK2,X0) | r1_orders_2(sK2,k1_yellow_0(sK2,X1),k1_yellow_0(sK2,X0))) )),
% 1.29/0.56    inference(resolution,[],[f82,f61])).
% 1.29/0.56  fof(f82,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2) | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) )),
% 1.29/0.56    inference(cnf_transformation,[],[f25])).
% 1.29/0.56  fof(f25,plain,(
% 1.29/0.56    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 1.29/0.56    inference(flattening,[],[f24])).
% 1.29/0.56  fof(f24,plain,(
% 1.29/0.56    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 1.29/0.56    inference(ennf_transformation,[],[f11])).
% 1.29/0.56  fof(f11,axiom,(
% 1.29/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_yellow_0)).
% 1.29/0.56  fof(f208,plain,(
% 1.29/0.56    ~spl7_9 | spl7_4 | ~spl7_3 | ~spl7_9),
% 1.29/0.56    inference(avatar_split_clause,[],[f205,f190,f118,f122,f190])).
% 1.29/0.56  fof(f122,plain,(
% 1.29/0.56    spl7_4 <=> u1_struct_0(sK2) = sK3),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.29/0.56  fof(f205,plain,(
% 1.29/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | u1_struct_0(sK2) = sK3 | ~r2_hidden(sK6(sK3,u1_struct_0(sK2)),sK3) | ~spl7_9),
% 1.29/0.56    inference(resolution,[],[f204,f93])).
% 1.29/0.56  fof(f93,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | X0 = X1 | ~r2_hidden(sK6(X0,X1),X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f55])).
% 1.29/0.56  fof(f55,plain,(
% 1.29/0.56    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK6(X0,X1),X1) | ~r2_hidden(sK6(X0,X1),X0)) & (r2_hidden(sK6(X0,X1),X1) | r2_hidden(sK6(X0,X1),X0))))),
% 1.29/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f53,f54])).
% 1.29/0.56  fof(f54,plain,(
% 1.29/0.56    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK6(X0,X1),X1) | ~r2_hidden(sK6(X0,X1),X0)) & (r2_hidden(sK6(X0,X1),X1) | r2_hidden(sK6(X0,X1),X0))))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f53,plain,(
% 1.29/0.56    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.29/0.56    inference(nnf_transformation,[],[f35])).
% 1.29/0.56  fof(f35,plain,(
% 1.29/0.56    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.29/0.56    inference(ennf_transformation,[],[f1])).
% 1.29/0.56  fof(f1,axiom,(
% 1.29/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 1.29/0.56  fof(f204,plain,(
% 1.29/0.56    ( ! [X0] : (r2_hidden(sK6(sK3,u1_struct_0(sK2)),X0) | ~m1_subset_1(sK3,k1_zfmisc_1(X0))) ) | ~spl7_9),
% 1.29/0.56    inference(resolution,[],[f191,f91])).
% 1.29/0.56  fof(f91,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.29/0.56    inference(cnf_transformation,[],[f34])).
% 1.29/0.56  fof(f34,plain,(
% 1.29/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f5])).
% 1.29/0.56  fof(f5,axiom,(
% 1.29/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.29/0.56  fof(f191,plain,(
% 1.29/0.56    r2_hidden(sK6(sK3,u1_struct_0(sK2)),sK3) | ~spl7_9),
% 1.29/0.56    inference(avatar_component_clause,[],[f190])).
% 1.29/0.56  fof(f203,plain,(
% 1.29/0.56    spl7_9 | spl7_4 | spl7_10),
% 1.29/0.56    inference(avatar_split_clause,[],[f202,f194,f122,f190])).
% 1.29/0.56  fof(f202,plain,(
% 1.29/0.56    u1_struct_0(sK2) = sK3 | r2_hidden(sK6(sK3,u1_struct_0(sK2)),sK3) | spl7_10),
% 1.29/0.56    inference(resolution,[],[f196,f92])).
% 1.29/0.56  fof(f92,plain,(
% 1.29/0.56    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | X0 = X1 | r2_hidden(sK6(X0,X1),X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f55])).
% 1.29/0.56  fof(f196,plain,(
% 1.29/0.56    ~r2_hidden(sK6(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)) | spl7_10),
% 1.29/0.56    inference(avatar_component_clause,[],[f194])).
% 1.29/0.56  fof(f161,plain,(
% 1.29/0.56    ~spl7_1 | ~spl7_4),
% 1.29/0.56    inference(avatar_contradiction_clause,[],[f158])).
% 1.29/0.56  fof(f158,plain,(
% 1.29/0.56    $false | (~spl7_1 | ~spl7_4)),
% 1.29/0.56    inference(resolution,[],[f156,f106])).
% 1.29/0.56  fof(f106,plain,(
% 1.29/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.29/0.56    inference(forward_demodulation,[],[f70,f69])).
% 1.29/0.56  fof(f69,plain,(
% 1.29/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.29/0.56    inference(cnf_transformation,[],[f3])).
% 1.29/0.56  fof(f3,axiom,(
% 1.29/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.29/0.56  fof(f70,plain,(
% 1.29/0.56    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.29/0.56    inference(cnf_transformation,[],[f4])).
% 1.29/0.56  fof(f4,axiom,(
% 1.29/0.56    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.29/0.56  fof(f156,plain,(
% 1.29/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(sK3)) | (~spl7_1 | ~spl7_4)),
% 1.29/0.56    inference(resolution,[],[f155,f95])).
% 1.29/0.56  fof(f95,plain,(
% 1.29/0.56    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 1.29/0.56    inference(equality_resolution,[],[f89])).
% 1.29/0.56  fof(f89,plain,(
% 1.29/0.56    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.29/0.56    inference(cnf_transformation,[],[f52])).
% 1.29/0.56  fof(f52,plain,(
% 1.29/0.56    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.56    inference(nnf_transformation,[],[f33])).
% 1.29/0.56  fof(f33,plain,(
% 1.29/0.56    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f15])).
% 1.29/0.56  fof(f15,axiom,(
% 1.29/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 1.29/0.56  fof(f155,plain,(
% 1.29/0.56    v1_subset_1(sK3,sK3) | (~spl7_1 | ~spl7_4)),
% 1.29/0.56    inference(forward_demodulation,[],[f98,f124])).
% 1.29/0.56  fof(f124,plain,(
% 1.29/0.56    u1_struct_0(sK2) = sK3 | ~spl7_4),
% 1.29/0.56    inference(avatar_component_clause,[],[f122])).
% 1.29/0.56  fof(f98,plain,(
% 1.29/0.56    v1_subset_1(sK3,u1_struct_0(sK2)) | ~spl7_1),
% 1.29/0.56    inference(avatar_component_clause,[],[f97])).
% 1.29/0.56  fof(f97,plain,(
% 1.29/0.56    spl7_1 <=> v1_subset_1(sK3,u1_struct_0(sK2))),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.29/0.56  fof(f154,plain,(
% 1.29/0.56    spl7_2 | ~spl7_6),
% 1.29/0.56    inference(avatar_contradiction_clause,[],[f152])).
% 1.29/0.56  fof(f152,plain,(
% 1.29/0.56    $false | (spl7_2 | ~spl7_6)),
% 1.29/0.56    inference(resolution,[],[f151,f102])).
% 1.29/0.56  fof(f102,plain,(
% 1.29/0.56    ~r2_hidden(k3_yellow_0(sK2),sK3) | spl7_2),
% 1.29/0.56    inference(avatar_component_clause,[],[f101])).
% 1.29/0.56  fof(f151,plain,(
% 1.29/0.56    r2_hidden(k3_yellow_0(sK2),sK3) | ~spl7_6),
% 1.29/0.56    inference(resolution,[],[f147,f107])).
% 1.29/0.56  fof(f107,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_subset_1(X0,sK3) | r2_hidden(X0,sK3)) )),
% 1.29/0.56    inference(resolution,[],[f88,f62])).
% 1.29/0.56  fof(f62,plain,(
% 1.29/0.56    ~v1_xboole_0(sK3)),
% 1.29/0.56    inference(cnf_transformation,[],[f45])).
% 1.29/0.56  fof(f88,plain,(
% 1.29/0.56    ( ! [X0,X1] : (v1_xboole_0(X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f32])).
% 1.29/0.56  fof(f32,plain,(
% 1.29/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.29/0.56    inference(flattening,[],[f31])).
% 1.29/0.56  fof(f31,plain,(
% 1.29/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.29/0.56    inference(ennf_transformation,[],[f7])).
% 1.29/0.56  fof(f7,axiom,(
% 1.29/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.29/0.56  fof(f147,plain,(
% 1.29/0.56    m1_subset_1(k3_yellow_0(sK2),sK3) | ~spl7_6),
% 1.29/0.56    inference(avatar_component_clause,[],[f145])).
% 1.29/0.56  fof(f145,plain,(
% 1.29/0.56    spl7_6 <=> m1_subset_1(k3_yellow_0(sK2),sK3)),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.29/0.56  fof(f150,plain,(
% 1.29/0.56    spl7_5),
% 1.29/0.56    inference(avatar_contradiction_clause,[],[f149])).
% 1.29/0.56  fof(f149,plain,(
% 1.29/0.56    $false | spl7_5),
% 1.29/0.56    inference(resolution,[],[f143,f61])).
% 1.29/0.56  fof(f143,plain,(
% 1.29/0.56    ~l1_orders_2(sK2) | spl7_5),
% 1.29/0.56    inference(avatar_component_clause,[],[f141])).
% 1.29/0.56  fof(f148,plain,(
% 1.29/0.56    ~spl7_5 | spl7_6 | ~spl7_4),
% 1.29/0.56    inference(avatar_split_clause,[],[f139,f122,f145,f141])).
% 1.29/0.56  fof(f139,plain,(
% 1.29/0.56    m1_subset_1(k3_yellow_0(sK2),sK3) | ~l1_orders_2(sK2) | ~spl7_4),
% 1.29/0.56    inference(superposition,[],[f71,f124])).
% 1.29/0.56  fof(f129,plain,(
% 1.29/0.56    spl7_3),
% 1.29/0.56    inference(avatar_contradiction_clause,[],[f127])).
% 1.29/0.56  fof(f127,plain,(
% 1.29/0.56    $false | spl7_3),
% 1.29/0.56    inference(resolution,[],[f120,f65])).
% 1.29/0.56  fof(f65,plain,(
% 1.29/0.56    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.29/0.56    inference(cnf_transformation,[],[f45])).
% 1.29/0.56  fof(f120,plain,(
% 1.29/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | spl7_3),
% 1.29/0.56    inference(avatar_component_clause,[],[f118])).
% 1.29/0.56  fof(f125,plain,(
% 1.29/0.56    ~spl7_3 | spl7_4 | spl7_1),
% 1.29/0.56    inference(avatar_split_clause,[],[f114,f97,f122,f118])).
% 1.29/0.56  fof(f114,plain,(
% 1.29/0.56    u1_struct_0(sK2) = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | spl7_1),
% 1.29/0.56    inference(resolution,[],[f90,f99])).
% 1.29/0.56  fof(f99,plain,(
% 1.29/0.56    ~v1_subset_1(sK3,u1_struct_0(sK2)) | spl7_1),
% 1.29/0.56    inference(avatar_component_clause,[],[f97])).
% 1.29/0.56  fof(f90,plain,(
% 1.29/0.56    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.29/0.56    inference(cnf_transformation,[],[f52])).
% 1.29/0.56  fof(f105,plain,(
% 1.29/0.56    spl7_1 | ~spl7_2),
% 1.29/0.56    inference(avatar_split_clause,[],[f66,f101,f97])).
% 1.29/0.56  fof(f66,plain,(
% 1.29/0.56    ~r2_hidden(k3_yellow_0(sK2),sK3) | v1_subset_1(sK3,u1_struct_0(sK2))),
% 1.29/0.56    inference(cnf_transformation,[],[f45])).
% 1.29/0.56  fof(f104,plain,(
% 1.29/0.56    ~spl7_1 | spl7_2),
% 1.29/0.56    inference(avatar_split_clause,[],[f67,f101,f97])).
% 1.29/0.56  fof(f67,plain,(
% 1.29/0.56    r2_hidden(k3_yellow_0(sK2),sK3) | ~v1_subset_1(sK3,u1_struct_0(sK2))),
% 1.29/0.56    inference(cnf_transformation,[],[f45])).
% 1.29/0.56  % SZS output end Proof for theBenchmark
% 1.29/0.56  % (21060)------------------------------
% 1.29/0.56  % (21060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (21060)Termination reason: Refutation
% 1.29/0.56  
% 1.29/0.56  % (21060)Memory used [KB]: 6396
% 1.29/0.56  % (21060)Time elapsed: 0.154 s
% 1.29/0.56  % (21060)------------------------------
% 1.29/0.56  % (21060)------------------------------
% 1.29/0.57  % (21047)Success in time 0.2 s
%------------------------------------------------------------------------------
