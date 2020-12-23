%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t36_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:52 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 454 expanded)
%              Number of leaves         :   53 ( 195 expanded)
%              Depth                    :   12
%              Number of atoms          :  831 (2280 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f376,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f123,f130,f137,f144,f151,f158,f165,f178,f179,f201,f210,f218,f232,f236,f237,f275,f288,f289,f292,f295,f298,f301,f305,f317,f324,f354,f365,f366,f369,f372,f375])).

fof(f375,plain,
    ( ~ spl12_20
    | ~ spl12_48 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | ~ spl12_20
    | ~ spl12_48 ),
    inference(subsumption_resolution,[],[f373,f200])).

fof(f200,plain,
    ( sP1(sK4)
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl12_20
  <=> sP1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f373,plain,
    ( ~ sP1(sK4)
    | ~ spl12_48 ),
    inference(resolution,[],[f341,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK7(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK7(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK7(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK7(X0),X0)
        & v7_waybel_0(sK7(X0))
        & v4_orders_2(sK7(X0))
        & ~ v2_struct_0(sK7(X0)) )
      | ~ sP1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f60,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK7(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK7(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK7(X0),X0)
        & v7_waybel_0(sK7(X0))
        & v4_orders_2(sK7(X0))
        & ~ v2_struct_0(sK7(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f341,plain,
    ( v2_struct_0(sK7(sK4))
    | ~ spl12_48 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl12_48
  <=> v2_struct_0(sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_48])])).

fof(f372,plain,
    ( ~ spl12_20
    | spl12_53 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | ~ spl12_20
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f370,f200])).

fof(f370,plain,
    ( ~ sP1(sK4)
    | ~ spl12_53 ),
    inference(resolution,[],[f353,f95])).

fof(f95,plain,(
    ! [X0] :
      ( v7_waybel_0(sK7(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f353,plain,
    ( ~ v7_waybel_0(sK7(sK4))
    | ~ spl12_53 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl12_53
  <=> ~ v7_waybel_0(sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_53])])).

fof(f369,plain,
    ( ~ spl12_20
    | spl12_51 ),
    inference(avatar_contradiction_clause,[],[f368])).

fof(f368,plain,
    ( $false
    | ~ spl12_20
    | ~ spl12_51 ),
    inference(subsumption_resolution,[],[f367,f200])).

fof(f367,plain,
    ( ~ sP1(sK4)
    | ~ spl12_51 ),
    inference(resolution,[],[f347,f94])).

fof(f94,plain,(
    ! [X0] :
      ( v4_orders_2(sK7(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f347,plain,
    ( ~ v4_orders_2(sK7(sK4))
    | ~ spl12_51 ),
    inference(avatar_component_clause,[],[f346])).

fof(f346,plain,
    ( spl12_51
  <=> ~ v4_orders_2(sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_51])])).

fof(f366,plain,
    ( spl12_48
    | ~ spl12_51
    | ~ spl12_53
    | ~ spl12_18
    | ~ spl12_22
    | ~ spl12_24
    | spl12_47 ),
    inference(avatar_split_clause,[],[f358,f334,f216,f208,f176,f352,f346,f340])).

fof(f176,plain,
    ( spl12_18
  <=> sP0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f208,plain,
    ( spl12_22
  <=> l1_waybel_0(sK7(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f216,plain,
    ( spl12_24
  <=> r2_hidden(sK7(sK4),k6_yellow_6(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f334,plain,
    ( spl12_47
  <=> ~ m1_subset_1(sK3(sK4,sK7(sK4)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_47])])).

fof(f358,plain,
    ( ~ v7_waybel_0(sK7(sK4))
    | ~ v4_orders_2(sK7(sK4))
    | v2_struct_0(sK7(sK4))
    | ~ spl12_18
    | ~ spl12_22
    | ~ spl12_24
    | ~ spl12_47 ),
    inference(subsumption_resolution,[],[f357,f217])).

fof(f217,plain,
    ( r2_hidden(sK7(sK4),k6_yellow_6(sK4))
    | ~ spl12_24 ),
    inference(avatar_component_clause,[],[f216])).

fof(f357,plain,
    ( ~ v7_waybel_0(sK7(sK4))
    | ~ v4_orders_2(sK7(sK4))
    | v2_struct_0(sK7(sK4))
    | ~ r2_hidden(sK7(sK4),k6_yellow_6(sK4))
    | ~ spl12_18
    | ~ spl12_22
    | ~ spl12_47 ),
    inference(subsumption_resolution,[],[f355,f209])).

fof(f209,plain,
    ( l1_waybel_0(sK7(sK4),sK4)
    | ~ spl12_22 ),
    inference(avatar_component_clause,[],[f208])).

fof(f355,plain,
    ( ~ l1_waybel_0(sK7(sK4),sK4)
    | ~ v7_waybel_0(sK7(sK4))
    | ~ v4_orders_2(sK7(sK4))
    | v2_struct_0(sK7(sK4))
    | ~ r2_hidden(sK7(sK4),k6_yellow_6(sK4))
    | ~ spl12_18
    | ~ spl12_47 ),
    inference(resolution,[],[f335,f307])).

fof(f307,plain,
    ( ! [X1] :
        ( m1_subset_1(sK3(sK4,X1),u1_struct_0(sK4))
        | ~ l1_waybel_0(X1,sK4)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ r2_hidden(X1,k6_yellow_6(sK4)) )
    | ~ spl12_18 ),
    inference(resolution,[],[f177,f71])).

fof(f71,plain,(
    ! [X0,X3] :
      ( ~ sP0(X0)
      | ~ r2_hidden(X3,k6_yellow_6(X0))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | m1_subset_1(sK3(X0,X3),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X2] :
              ( ~ r3_waybel_9(X0,sK2(X0),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(sK2(X0),k6_yellow_6(X0))
          & l1_waybel_0(sK2(X0),X0)
          & v7_waybel_0(sK2(X0))
          & v4_orders_2(sK2(X0))
          & ~ v2_struct_0(sK2(X0)) ) )
      & ( ! [X3] :
            ( ( r3_waybel_9(X0,X3,sK3(X0,X3))
              & m1_subset_1(sK3(X0,X3),u1_struct_0(X0)) )
            | ~ r2_hidden(X3,k6_yellow_6(X0))
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f48,f50,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK2(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK2(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK2(X0),X0)
        & v7_waybel_0(sK2(X0))
        & v4_orders_2(sK2(X0))
        & ~ v2_struct_0(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK3(X0,X3))
        & m1_subset_1(sK3(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r2_hidden(X1,k6_yellow_6(X0))
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) ) )
      & ( ! [X3] :
            ( ? [X4] :
                ( r3_waybel_9(X0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_hidden(X3,k6_yellow_6(X0))
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r2_hidden(X1,k6_yellow_6(X0))
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) ) )
      & ( ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ r2_hidden(X1,k6_yellow_6(X0))
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f177,plain,
    ( sP0(sK4)
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f176])).

fof(f335,plain,
    ( ~ m1_subset_1(sK3(sK4,sK7(sK4)),u1_struct_0(sK4))
    | ~ spl12_47 ),
    inference(avatar_component_clause,[],[f334])).

fof(f365,plain,
    ( ~ spl12_55
    | spl12_47 ),
    inference(avatar_split_clause,[],[f356,f334,f363])).

fof(f363,plain,
    ( spl12_55
  <=> ~ r2_hidden(sK3(sK4,sK7(sK4)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_55])])).

fof(f356,plain,
    ( ~ r2_hidden(sK3(sK4,sK7(sK4)),u1_struct_0(sK4))
    | ~ spl12_47 ),
    inference(resolution,[],[f335,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t36_yellow19.p',t1_subset)).

fof(f354,plain,
    ( ~ spl12_47
    | spl12_48
    | ~ spl12_51
    | ~ spl12_53
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_24 ),
    inference(avatar_split_clause,[],[f328,f216,f208,f199,f176,f352,f346,f340,f334])).

fof(f328,plain,
    ( ~ v7_waybel_0(sK7(sK4))
    | ~ v4_orders_2(sK7(sK4))
    | v2_struct_0(sK7(sK4))
    | ~ m1_subset_1(sK3(sK4,sK7(sK4)),u1_struct_0(sK4))
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_24 ),
    inference(subsumption_resolution,[],[f327,f217])).

fof(f327,plain,
    ( ~ v7_waybel_0(sK7(sK4))
    | ~ v4_orders_2(sK7(sK4))
    | v2_struct_0(sK7(sK4))
    | ~ r2_hidden(sK7(sK4),k6_yellow_6(sK4))
    | ~ m1_subset_1(sK3(sK4,sK7(sK4)),u1_struct_0(sK4))
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f325,f209])).

fof(f325,plain,
    ( ~ l1_waybel_0(sK7(sK4),sK4)
    | ~ v7_waybel_0(sK7(sK4))
    | ~ v4_orders_2(sK7(sK4))
    | v2_struct_0(sK7(sK4))
    | ~ r2_hidden(sK7(sK4),k6_yellow_6(sK4))
    | ~ m1_subset_1(sK3(sK4,sK7(sK4)),u1_struct_0(sK4))
    | ~ spl12_18
    | ~ spl12_20 ),
    inference(resolution,[],[f306,f302])).

fof(f302,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK4,sK7(sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | ~ spl12_20 ),
    inference(resolution,[],[f200,f98])).

fof(f98,plain,(
    ! [X2,X0] :
      ( ~ sP1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,sK7(X0),X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f306,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK4,X0,sK3(sK4,X0))
        | ~ l1_waybel_0(X0,sK4)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ r2_hidden(X0,k6_yellow_6(sK4)) )
    | ~ spl12_18 ),
    inference(resolution,[],[f177,f72])).

fof(f72,plain,(
    ! [X0,X3] :
      ( ~ sP0(X0)
      | ~ r2_hidden(X3,k6_yellow_6(X0))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | r3_waybel_9(X0,X3,sK3(X0,X3)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f324,plain,
    ( ~ spl12_45
    | ~ spl12_24 ),
    inference(avatar_split_clause,[],[f309,f216,f322])).

fof(f322,plain,
    ( spl12_45
  <=> ~ r2_hidden(k6_yellow_6(sK4),sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_45])])).

fof(f309,plain,
    ( ~ r2_hidden(k6_yellow_6(sK4),sK7(sK4))
    | ~ spl12_24 ),
    inference(resolution,[],[f217,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t36_yellow19.p',antisymmetry_r2_hidden)).

fof(f317,plain,
    ( ~ spl12_43
    | ~ spl12_24 ),
    inference(avatar_split_clause,[],[f310,f216,f315])).

fof(f315,plain,
    ( spl12_43
  <=> ~ v1_xboole_0(k6_yellow_6(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_43])])).

fof(f310,plain,
    ( ~ v1_xboole_0(k6_yellow_6(sK4))
    | ~ spl12_24 ),
    inference(resolution,[],[f217,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t36_yellow19.p',t7_boole)).

fof(f305,plain,
    ( spl12_18
    | ~ spl12_34 ),
    inference(avatar_split_clause,[],[f299,f261,f176])).

fof(f261,plain,
    ( spl12_34
  <=> v2_struct_0(sK2(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_34])])).

fof(f299,plain,
    ( sP0(sK4)
    | ~ spl12_34 ),
    inference(resolution,[],[f262,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK2(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f262,plain,
    ( v2_struct_0(sK2(sK4))
    | ~ spl12_34 ),
    inference(avatar_component_clause,[],[f261])).

fof(f301,plain,
    ( spl12_19
    | ~ spl12_34 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | ~ spl12_19
    | ~ spl12_34 ),
    inference(subsumption_resolution,[],[f299,f174])).

fof(f174,plain,
    ( ~ sP0(sK4)
    | ~ spl12_19 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl12_19
  <=> ~ sP0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f298,plain,
    ( spl12_19
    | spl12_39 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | ~ spl12_19
    | ~ spl12_39 ),
    inference(subsumption_resolution,[],[f296,f174])).

fof(f296,plain,
    ( sP0(sK4)
    | ~ spl12_39 ),
    inference(resolution,[],[f274,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v7_waybel_0(sK2(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f274,plain,
    ( ~ v7_waybel_0(sK2(sK4))
    | ~ spl12_39 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl12_39
  <=> ~ v7_waybel_0(sK2(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_39])])).

fof(f295,plain,
    ( spl12_19
    | spl12_37 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | ~ spl12_19
    | ~ spl12_37 ),
    inference(subsumption_resolution,[],[f293,f174])).

fof(f293,plain,
    ( sP0(sK4)
    | ~ spl12_37 ),
    inference(resolution,[],[f268,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v4_orders_2(sK2(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f268,plain,
    ( ~ v4_orders_2(sK2(sK4))
    | ~ spl12_37 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl12_37
  <=> ~ v4_orders_2(sK2(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_37])])).

fof(f292,plain,
    ( spl12_19
    | spl12_33 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | ~ spl12_19
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f290,f174])).

fof(f290,plain,
    ( sP0(sK4)
    | ~ spl12_33 ),
    inference(resolution,[],[f256,f76])).

fof(f76,plain,(
    ! [X0] :
      ( l1_waybel_0(sK2(X0),X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f256,plain,
    ( ~ l1_waybel_0(sK2(sK4),sK4)
    | ~ spl12_33 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl12_33
  <=> ~ l1_waybel_0(sK2(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_33])])).

fof(f289,plain,
    ( spl12_34
    | ~ spl12_37
    | ~ spl12_39
    | ~ spl12_33
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_16
    | spl12_31 ),
    inference(avatar_split_clause,[],[f281,f249,f170,f128,f121,f114,f255,f273,f267,f261])).

fof(f114,plain,
    ( spl12_1
  <=> ~ v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f121,plain,
    ( spl12_2
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f128,plain,
    ( spl12_4
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f170,plain,
    ( spl12_16
  <=> v1_compts_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f249,plain,
    ( spl12_31
  <=> ~ m1_subset_1(sK6(sK4,sK2(sK4)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).

fof(f281,plain,
    ( ~ l1_waybel_0(sK2(sK4),sK4)
    | ~ v7_waybel_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | v2_struct_0(sK2(sK4))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_16
    | ~ spl12_31 ),
    inference(subsumption_resolution,[],[f280,f115])).

fof(f115,plain,
    ( ~ v2_struct_0(sK4)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f280,plain,
    ( ~ l1_waybel_0(sK2(sK4),sK4)
    | ~ v7_waybel_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | v2_struct_0(sK2(sK4))
    | v2_struct_0(sK4)
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_16
    | ~ spl12_31 ),
    inference(subsumption_resolution,[],[f279,f122])).

fof(f122,plain,
    ( v2_pre_topc(sK4)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f279,plain,
    ( ~ l1_waybel_0(sK2(sK4),sK4)
    | ~ v7_waybel_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | v2_struct_0(sK2(sK4))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_4
    | ~ spl12_16
    | ~ spl12_31 ),
    inference(subsumption_resolution,[],[f278,f129])).

fof(f129,plain,
    ( l1_pre_topc(sK4)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f278,plain,
    ( ~ l1_waybel_0(sK2(sK4),sK4)
    | ~ v7_waybel_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | v2_struct_0(sK2(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_16
    | ~ spl12_31 ),
    inference(subsumption_resolution,[],[f276,f171])).

fof(f171,plain,
    ( v1_compts_1(sK4)
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f170])).

fof(f276,plain,
    ( ~ l1_waybel_0(sK2(sK4),sK4)
    | ~ v7_waybel_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | v2_struct_0(sK2(sK4))
    | ~ v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_31 ),
    inference(resolution,[],[f250,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK6(X0,X1))
            & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK6(X0,X1))
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t36_yellow19.p',l37_yellow19)).

fof(f250,plain,
    ( ~ m1_subset_1(sK6(sK4,sK2(sK4)),u1_struct_0(sK4))
    | ~ spl12_31 ),
    inference(avatar_component_clause,[],[f249])).

fof(f288,plain,
    ( ~ spl12_41
    | spl12_31 ),
    inference(avatar_split_clause,[],[f277,f249,f286])).

fof(f286,plain,
    ( spl12_41
  <=> ~ r2_hidden(sK6(sK4,sK2(sK4)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_41])])).

fof(f277,plain,
    ( ~ r2_hidden(sK6(sK4,sK2(sK4)),u1_struct_0(sK4))
    | ~ spl12_31 ),
    inference(resolution,[],[f250,f102])).

fof(f275,plain,
    ( ~ spl12_31
    | ~ spl12_33
    | spl12_34
    | ~ spl12_37
    | ~ spl12_39
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_16
    | spl12_19 ),
    inference(avatar_split_clause,[],[f244,f173,f170,f128,f121,f114,f273,f267,f261,f255,f249])).

fof(f244,plain,
    ( ~ v7_waybel_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | v2_struct_0(sK2(sK4))
    | ~ l1_waybel_0(sK2(sK4),sK4)
    | ~ m1_subset_1(sK6(sK4,sK2(sK4)),u1_struct_0(sK4))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_16
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f243,f174])).

fof(f243,plain,
    ( ~ v7_waybel_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | v2_struct_0(sK2(sK4))
    | ~ l1_waybel_0(sK2(sK4),sK4)
    | sP0(sK4)
    | ~ m1_subset_1(sK6(sK4,sK2(sK4)),u1_struct_0(sK4))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_16 ),
    inference(resolution,[],[f242,f78])).

fof(f78,plain,(
    ! [X2,X0] :
      ( ~ r3_waybel_9(X0,sK2(X0),X2)
      | sP0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f242,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK4,X0,sK6(sK4,X0))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK4) )
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_16 ),
    inference(subsumption_resolution,[],[f241,f115])).

fof(f241,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK4)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r3_waybel_9(sK4,X0,sK6(sK4,X0))
        | v2_struct_0(sK4) )
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_16 ),
    inference(subsumption_resolution,[],[f240,f122])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK4)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r3_waybel_9(sK4,X0,sK6(sK4,X0))
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl12_4
    | ~ spl12_16 ),
    inference(subsumption_resolution,[],[f239,f129])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK4)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r3_waybel_9(sK4,X0,sK6(sK4,X0))
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl12_16 ),
    inference(resolution,[],[f92,f171])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_compts_1(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | r3_waybel_9(X0,X1,sK6(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f237,plain,
    ( spl12_16
    | spl12_20
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f219,f128,f121,f114,f199,f170])).

fof(f219,plain,
    ( sP1(sK4)
    | v1_compts_1(sK4)
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f192,f115])).

fof(f192,plain,
    ( sP1(sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f191,f129])).

fof(f191,plain,
    ( sP1(sK4)
    | ~ l1_pre_topc(sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_2 ),
    inference(resolution,[],[f99,f122])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | sP1(X0)
      | ~ l1_pre_topc(X0)
      | v1_compts_1(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | sP1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f36,f45])).

fof(f36,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r3_waybel_9(X0,X1,X2) )
                & r2_hidden(X1,k6_yellow_6(X0)) ) )
       => v1_compts_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t36_yellow19.p',l38_yellow19)).

fof(f236,plain,
    ( ~ spl12_4
    | spl12_27 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl12_4
    | ~ spl12_27 ),
    inference(subsumption_resolution,[],[f233,f129])).

fof(f233,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ spl12_27 ),
    inference(resolution,[],[f225,f87])).

fof(f87,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t36_yellow19.p',dt_l1_pre_topc)).

fof(f225,plain,
    ( ~ l1_struct_0(sK4)
    | ~ spl12_27 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl12_27
  <=> ~ l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_27])])).

fof(f232,plain,
    ( ~ spl12_27
    | spl12_28
    | ~ spl12_22 ),
    inference(avatar_split_clause,[],[f211,f208,f230,f224])).

fof(f230,plain,
    ( spl12_28
  <=> l1_orders_2(sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).

fof(f211,plain,
    ( l1_orders_2(sK7(sK4))
    | ~ l1_struct_0(sK4)
    | ~ spl12_22 ),
    inference(resolution,[],[f209,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | l1_orders_2(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t36_yellow19.p',dt_l1_waybel_0)).

fof(f218,plain,
    ( spl12_24
    | ~ spl12_20 ),
    inference(avatar_split_clause,[],[f202,f199,f216])).

fof(f202,plain,
    ( r2_hidden(sK7(sK4),k6_yellow_6(sK4))
    | ~ spl12_20 ),
    inference(resolution,[],[f200,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | r2_hidden(sK7(X0),k6_yellow_6(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f210,plain,
    ( spl12_22
    | ~ spl12_20 ),
    inference(avatar_split_clause,[],[f203,f199,f208])).

fof(f203,plain,
    ( l1_waybel_0(sK7(sK4),sK4)
    | ~ spl12_20 ),
    inference(resolution,[],[f200,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | l1_waybel_0(sK7(X0),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f201,plain,
    ( spl12_20
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | spl12_17 ),
    inference(avatar_split_clause,[],[f194,f167,f128,f121,f114,f199])).

fof(f167,plain,
    ( spl12_17
  <=> ~ v1_compts_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).

fof(f194,plain,
    ( sP1(sK4)
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_17 ),
    inference(subsumption_resolution,[],[f193,f115])).

fof(f193,plain,
    ( sP1(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_17 ),
    inference(subsumption_resolution,[],[f192,f168])).

fof(f168,plain,
    ( ~ v1_compts_1(sK4)
    | ~ spl12_17 ),
    inference(avatar_component_clause,[],[f167])).

fof(f179,plain,
    ( ~ spl12_17
    | ~ spl12_19 ),
    inference(avatar_split_clause,[],[f83,f173,f167])).

fof(f83,plain,
    ( ~ sP0(sK4)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( ( ~ sP0(sK4)
      | ~ v1_compts_1(sK4) )
    & ( sP0(sK4)
      | v1_compts_1(sK4) )
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f53,f54])).

fof(f54,plain,
    ( ? [X0] :
        ( ( ~ sP0(X0)
          | ~ v1_compts_1(X0) )
        & ( sP0(X0)
          | v1_compts_1(X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ~ sP0(sK4)
        | ~ v1_compts_1(sK4) )
      & ( sP0(sK4)
        | v1_compts_1(sK4) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ? [X0] :
      ( ( ~ sP0(X0)
        | ~ v1_compts_1(X0) )
      & ( sP0(X0)
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ? [X0] :
      ( ( ~ sP0(X0)
        | ~ v1_compts_1(X0) )
      & ( sP0(X0)
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> sP0(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f27,f43])).

fof(f27,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_compts_1(X0)
        <=> ! [X1] :
              ( ( l1_waybel_0(X1,X0)
                & v7_waybel_0(X1)
                & v4_orders_2(X1)
                & ~ v2_struct_0(X1) )
             => ~ ( ! [X2] :
                      ( m1_subset_1(X2,u1_struct_0(X0))
                     => ~ r3_waybel_9(X0,X1,X2) )
                  & r2_hidden(X1,k6_yellow_6(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r3_waybel_9(X0,X1,X2) )
                & r2_hidden(X1,k6_yellow_6(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t36_yellow19.p',t36_yellow19)).

fof(f178,plain,
    ( spl12_16
    | spl12_18 ),
    inference(avatar_split_clause,[],[f82,f176,f170])).

fof(f82,plain,
    ( sP0(sK4)
    | v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f165,plain,(
    spl12_14 ),
    inference(avatar_split_clause,[],[f85,f163])).

fof(f163,plain,
    ( spl12_14
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f85,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t36_yellow19.p',d2_xboole_0)).

fof(f158,plain,(
    spl12_12 ),
    inference(avatar_split_clause,[],[f108,f156])).

fof(f156,plain,
    ( spl12_12
  <=> l1_struct_0(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f108,plain,(
    l1_struct_0(sK11) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    l1_struct_0(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f8,f69])).

fof(f69,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK11) ),
    introduced(choice_axiom,[])).

fof(f8,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t36_yellow19.p',existence_l1_struct_0)).

fof(f151,plain,(
    spl12_10 ),
    inference(avatar_split_clause,[],[f107,f149])).

fof(f149,plain,
    ( spl12_10
  <=> l1_pre_topc(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f107,plain,(
    l1_pre_topc(sK10) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    l1_pre_topc(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f14,f67])).

fof(f67,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK10) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t36_yellow19.p',existence_l1_pre_topc)).

fof(f144,plain,(
    spl12_8 ),
    inference(avatar_split_clause,[],[f106,f142])).

fof(f142,plain,
    ( spl12_8
  <=> l1_orders_2(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f106,plain,(
    l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    l1_orders_2(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f7,f65])).

fof(f65,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK9) ),
    introduced(choice_axiom,[])).

fof(f7,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t36_yellow19.p',existence_l1_orders_2)).

fof(f137,plain,(
    spl12_6 ),
    inference(avatar_split_clause,[],[f84,f135])).

fof(f135,plain,
    ( spl12_6
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f84,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t36_yellow19.p',dt_o_0_0_xboole_0)).

fof(f130,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f81,f128])).

fof(f81,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f123,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f80,f121])).

fof(f80,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f116,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f79,f114])).

fof(f79,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
