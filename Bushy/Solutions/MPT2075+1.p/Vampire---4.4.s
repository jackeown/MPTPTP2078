%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t35_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:52 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  256 ( 562 expanded)
%              Number of leaves         :   66 ( 245 expanded)
%              Depth                    :   12
%              Number of atoms          :  927 (2575 expanded)
%              Number of equality atoms :    9 (  22 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f461,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f122,f129,f136,f143,f150,f157,f164,f177,f178,f198,f207,f215,f229,f233,f234,f272,f278,f281,f284,f287,f291,f305,f312,f319,f333,f350,f354,f361,f368,f388,f391,f394,f397,f406,f421,f431,f438,f445,f446,f460])).

fof(f460,plain,
    ( spl12_19
    | ~ spl12_34 ),
    inference(avatar_contradiction_clause,[],[f459])).

fof(f459,plain,
    ( $false
    | ~ spl12_19
    | ~ spl12_34 ),
    inference(subsumption_resolution,[],[f458,f173])).

fof(f173,plain,
    ( ~ sP0(sK4)
    | ~ spl12_19 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl12_19
  <=> ~ sP0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f458,plain,
    ( sP0(sK4)
    | ~ spl12_34 ),
    inference(resolution,[],[f259,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK2(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X2] :
              ( ~ r3_waybel_9(X0,sK2(X0),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(sK2(X0),X0)
          & v7_waybel_0(sK2(X0))
          & v4_orders_2(sK2(X0))
          & ~ v2_struct_0(sK2(X0)) ) )
      & ( ! [X3] :
            ( ( r3_waybel_9(X0,X3,sK3(X0,X3))
              & m1_subset_1(sK3(X0,X3),u1_struct_0(X0)) )
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
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK2(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
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
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) ) )
      & ( ! [X3] :
            ( ? [X4] :
                ( r3_waybel_9(X0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
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
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) ) )
      & ( ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
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
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f259,plain,
    ( v2_struct_0(sK2(sK4))
    | ~ spl12_34 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl12_34
  <=> v2_struct_0(sK2(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_34])])).

fof(f446,plain,
    ( spl12_56
    | ~ spl12_59
    | ~ spl12_61
    | ~ spl12_18
    | ~ spl12_22
    | spl12_53 ),
    inference(avatar_split_clause,[],[f424,f356,f205,f175,f386,f380,f374])).

fof(f374,plain,
    ( spl12_56
  <=> v2_struct_0(sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_56])])).

fof(f380,plain,
    ( spl12_59
  <=> ~ v4_orders_2(sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_59])])).

fof(f386,plain,
    ( spl12_61
  <=> ~ v7_waybel_0(sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_61])])).

fof(f175,plain,
    ( spl12_18
  <=> sP0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f205,plain,
    ( spl12_22
  <=> l1_waybel_0(sK7(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f356,plain,
    ( spl12_53
  <=> ~ m1_subset_1(sK3(sK4,sK7(sK4)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_53])])).

fof(f424,plain,
    ( ~ v7_waybel_0(sK7(sK4))
    | ~ v4_orders_2(sK7(sK4))
    | v2_struct_0(sK7(sK4))
    | ~ spl12_18
    | ~ spl12_22
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f422,f206])).

fof(f206,plain,
    ( l1_waybel_0(sK7(sK4),sK4)
    | ~ spl12_22 ),
    inference(avatar_component_clause,[],[f205])).

fof(f422,plain,
    ( ~ v7_waybel_0(sK7(sK4))
    | ~ v4_orders_2(sK7(sK4))
    | v2_struct_0(sK7(sK4))
    | ~ l1_waybel_0(sK7(sK4),sK4)
    | ~ spl12_18
    | ~ spl12_53 ),
    inference(resolution,[],[f357,f293])).

fof(f293,plain,
    ( ! [X1] :
        ( m1_subset_1(sK3(sK4,X1),u1_struct_0(sK4))
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,sK4) )
    | ~ spl12_18 ),
    inference(resolution,[],[f176,f71])).

fof(f71,plain,(
    ! [X0,X3] :
      ( ~ sP0(X0)
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | m1_subset_1(sK3(X0,X3),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f176,plain,
    ( sP0(sK4)
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f175])).

fof(f357,plain,
    ( ~ m1_subset_1(sK3(sK4,sK7(sK4)),u1_struct_0(sK4))
    | ~ spl12_53 ),
    inference(avatar_component_clause,[],[f356])).

fof(f445,plain,
    ( ~ spl12_71
    | spl12_53
    | ~ spl12_62 ),
    inference(avatar_split_clause,[],[f423,f404,f356,f443])).

fof(f443,plain,
    ( spl12_71
  <=> ~ m1_subset_1(sK3(sK4,sK7(sK4)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_71])])).

fof(f404,plain,
    ( spl12_62
  <=> u1_struct_0(sK4) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_62])])).

fof(f423,plain,
    ( ~ m1_subset_1(sK3(sK4,sK7(sK4)),k1_xboole_0)
    | ~ spl12_53
    | ~ spl12_62 ),
    inference(superposition,[],[f357,f405])).

fof(f405,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | ~ spl12_62 ),
    inference(avatar_component_clause,[],[f404])).

fof(f438,plain,
    ( ~ spl12_69
    | spl12_55
    | ~ spl12_62 ),
    inference(avatar_split_clause,[],[f408,f404,f366,f436])).

fof(f436,plain,
    ( spl12_69
  <=> ~ r2_hidden(k1_xboole_0,sK3(sK4,sK7(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_69])])).

fof(f366,plain,
    ( spl12_55
  <=> ~ r2_hidden(u1_struct_0(sK4),sK3(sK4,sK7(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_55])])).

fof(f408,plain,
    ( ~ r2_hidden(k1_xboole_0,sK3(sK4,sK7(sK4)))
    | ~ spl12_55
    | ~ spl12_62 ),
    inference(superposition,[],[f367,f405])).

fof(f367,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),sK3(sK4,sK7(sK4)))
    | ~ spl12_55 ),
    inference(avatar_component_clause,[],[f366])).

fof(f431,plain,
    ( ~ spl12_67
    | spl12_51
    | ~ spl12_62 ),
    inference(avatar_split_clause,[],[f414,f404,f345,f429])).

fof(f429,plain,
    ( spl12_67
  <=> ~ r2_hidden(sK3(sK4,sK7(sK4)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_67])])).

fof(f345,plain,
    ( spl12_51
  <=> ~ r2_hidden(sK3(sK4,sK7(sK4)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_51])])).

fof(f414,plain,
    ( ~ r2_hidden(sK3(sK4,sK7(sK4)),k1_xboole_0)
    | ~ spl12_51
    | ~ spl12_62 ),
    inference(superposition,[],[f346,f405])).

fof(f346,plain,
    ( ~ r2_hidden(sK3(sK4,sK7(sK4)),u1_struct_0(sK4))
    | ~ spl12_51 ),
    inference(avatar_component_clause,[],[f345])).

fof(f421,plain,
    ( ~ spl12_65
    | spl12_31
    | ~ spl12_62 ),
    inference(avatar_split_clause,[],[f410,f404,f246,f419])).

fof(f419,plain,
    ( spl12_65
  <=> ~ m1_subset_1(sK6(sK4,sK2(sK4)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_65])])).

fof(f246,plain,
    ( spl12_31
  <=> ~ m1_subset_1(sK6(sK4,sK2(sK4)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).

fof(f410,plain,
    ( ~ m1_subset_1(sK6(sK4,sK2(sK4)),k1_xboole_0)
    | ~ spl12_31
    | ~ spl12_62 ),
    inference(superposition,[],[f247,f405])).

fof(f247,plain,
    ( ~ m1_subset_1(sK6(sK4,sK2(sK4)),u1_struct_0(sK4))
    | ~ spl12_31 ),
    inference(avatar_component_clause,[],[f246])).

fof(f406,plain,
    ( spl12_62
    | ~ spl12_46 ),
    inference(avatar_split_clause,[],[f399,f328,f404])).

fof(f328,plain,
    ( spl12_46
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_46])])).

fof(f399,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | ~ spl12_46 ),
    inference(resolution,[],[f329,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t35_yellow19.p',t6_boole)).

fof(f329,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ spl12_46 ),
    inference(avatar_component_clause,[],[f328])).

fof(f397,plain,
    ( ~ spl12_20
    | ~ spl12_56 ),
    inference(avatar_contradiction_clause,[],[f396])).

fof(f396,plain,
    ( $false
    | ~ spl12_20
    | ~ spl12_56 ),
    inference(subsumption_resolution,[],[f395,f197])).

fof(f197,plain,
    ( sP1(sK4)
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl12_20
  <=> sP1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f395,plain,
    ( ~ sP1(sK4)
    | ~ spl12_56 ),
    inference(resolution,[],[f375,f92])).

fof(f92,plain,(
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

fof(f375,plain,
    ( v2_struct_0(sK7(sK4))
    | ~ spl12_56 ),
    inference(avatar_component_clause,[],[f374])).

fof(f394,plain,
    ( ~ spl12_20
    | spl12_61 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | ~ spl12_20
    | ~ spl12_61 ),
    inference(subsumption_resolution,[],[f392,f197])).

fof(f392,plain,
    ( ~ sP1(sK4)
    | ~ spl12_61 ),
    inference(resolution,[],[f387,f94])).

fof(f94,plain,(
    ! [X0] :
      ( v7_waybel_0(sK7(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f387,plain,
    ( ~ v7_waybel_0(sK7(sK4))
    | ~ spl12_61 ),
    inference(avatar_component_clause,[],[f386])).

fof(f391,plain,
    ( ~ spl12_20
    | spl12_59 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | ~ spl12_20
    | ~ spl12_59 ),
    inference(subsumption_resolution,[],[f389,f197])).

fof(f389,plain,
    ( ~ sP1(sK4)
    | ~ spl12_59 ),
    inference(resolution,[],[f381,f93])).

fof(f93,plain,(
    ! [X0] :
      ( v4_orders_2(sK7(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f381,plain,
    ( ~ v4_orders_2(sK7(sK4))
    | ~ spl12_59 ),
    inference(avatar_component_clause,[],[f380])).

fof(f388,plain,
    ( spl12_56
    | ~ spl12_59
    | ~ spl12_61
    | ~ spl12_53
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22 ),
    inference(avatar_split_clause,[],[f322,f205,f196,f175,f356,f386,f380,f374])).

fof(f322,plain,
    ( ~ m1_subset_1(sK3(sK4,sK7(sK4)),u1_struct_0(sK4))
    | ~ v7_waybel_0(sK7(sK4))
    | ~ v4_orders_2(sK7(sK4))
    | v2_struct_0(sK7(sK4))
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f321,f206])).

fof(f321,plain,
    ( ~ m1_subset_1(sK3(sK4,sK7(sK4)),u1_struct_0(sK4))
    | ~ v7_waybel_0(sK7(sK4))
    | ~ v4_orders_2(sK7(sK4))
    | v2_struct_0(sK7(sK4))
    | ~ l1_waybel_0(sK7(sK4),sK4)
    | ~ spl12_18
    | ~ spl12_20 ),
    inference(resolution,[],[f288,f292])).

fof(f292,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK4,X0,sK3(sK4,X0))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK4) )
    | ~ spl12_18 ),
    inference(resolution,[],[f176,f72])).

fof(f72,plain,(
    ! [X0,X3] :
      ( ~ sP0(X0)
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | r3_waybel_9(X0,X3,sK3(X0,X3)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK4,sK7(sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | ~ spl12_20 ),
    inference(resolution,[],[f197,f97])).

fof(f97,plain,(
    ! [X2,X0] :
      ( ~ sP1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,sK7(X0),X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f368,plain,
    ( ~ spl12_55
    | ~ spl12_50 ),
    inference(avatar_split_clause,[],[f352,f348,f366])).

fof(f348,plain,
    ( spl12_50
  <=> r2_hidden(sK3(sK4,sK7(sK4)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_50])])).

fof(f352,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),sK3(sK4,sK7(sK4)))
    | ~ spl12_50 ),
    inference(resolution,[],[f349,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t35_yellow19.p',antisymmetry_r2_hidden)).

fof(f349,plain,
    ( r2_hidden(sK3(sK4,sK7(sK4)),u1_struct_0(sK4))
    | ~ spl12_50 ),
    inference(avatar_component_clause,[],[f348])).

fof(f361,plain,
    ( spl12_52
    | ~ spl12_50 ),
    inference(avatar_split_clause,[],[f351,f348,f359])).

fof(f359,plain,
    ( spl12_52
  <=> m1_subset_1(sK3(sK4,sK7(sK4)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_52])])).

fof(f351,plain,
    ( m1_subset_1(sK3(sK4,sK7(sK4)),u1_struct_0(sK4))
    | ~ spl12_50 ),
    inference(resolution,[],[f349,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t35_yellow19.p',t1_subset)).

fof(f354,plain,
    ( ~ spl12_47
    | ~ spl12_50 ),
    inference(avatar_split_clause,[],[f353,f348,f325])).

fof(f325,plain,
    ( spl12_47
  <=> ~ v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_47])])).

fof(f353,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ spl12_50 ),
    inference(resolution,[],[f349,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t35_yellow19.p',t7_boole)).

fof(f350,plain,
    ( spl12_50
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_48 ),
    inference(avatar_split_clause,[],[f343,f331,f205,f196,f348])).

fof(f331,plain,
    ( spl12_48
  <=> ! [X0] :
        ( ~ v7_waybel_0(X0)
        | r2_hidden(sK3(sK4,X0),u1_struct_0(sK4))
        | ~ l1_waybel_0(X0,sK4)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_48])])).

fof(f343,plain,
    ( r2_hidden(sK3(sK4,sK7(sK4)),u1_struct_0(sK4))
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_48 ),
    inference(subsumption_resolution,[],[f342,f197])).

fof(f342,plain,
    ( r2_hidden(sK3(sK4,sK7(sK4)),u1_struct_0(sK4))
    | ~ sP1(sK4)
    | ~ spl12_22
    | ~ spl12_48 ),
    inference(resolution,[],[f339,f206])).

fof(f339,plain,
    ( ! [X1] :
        ( ~ l1_waybel_0(sK7(X1),sK4)
        | r2_hidden(sK3(sK4,sK7(X1)),u1_struct_0(sK4))
        | ~ sP1(X1) )
    | ~ spl12_48 ),
    inference(subsumption_resolution,[],[f338,f93])).

fof(f338,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK4,sK7(X1)),u1_struct_0(sK4))
        | ~ l1_waybel_0(sK7(X1),sK4)
        | ~ v4_orders_2(sK7(X1))
        | ~ sP1(X1) )
    | ~ spl12_48 ),
    inference(subsumption_resolution,[],[f335,f92])).

fof(f335,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK4,sK7(X1)),u1_struct_0(sK4))
        | ~ l1_waybel_0(sK7(X1),sK4)
        | v2_struct_0(sK7(X1))
        | ~ v4_orders_2(sK7(X1))
        | ~ sP1(X1) )
    | ~ spl12_48 ),
    inference(resolution,[],[f332,f94])).

fof(f332,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(X0)
        | r2_hidden(sK3(sK4,X0),u1_struct_0(sK4))
        | ~ l1_waybel_0(X0,sK4)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0) )
    | ~ spl12_48 ),
    inference(avatar_component_clause,[],[f331])).

fof(f333,plain,
    ( spl12_46
    | spl12_48
    | ~ spl12_18 ),
    inference(avatar_split_clause,[],[f323,f175,f331,f328])).

fof(f323,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK4)
        | v1_xboole_0(u1_struct_0(sK4))
        | r2_hidden(sK3(sK4,X0),u1_struct_0(sK4)) )
    | ~ spl12_18 ),
    inference(resolution,[],[f293,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t35_yellow19.p',t2_subset)).

fof(f319,plain,
    ( ~ spl12_45
    | ~ spl12_24 ),
    inference(avatar_split_clause,[],[f297,f213,f317])).

fof(f317,plain,
    ( spl12_45
  <=> ~ r2_hidden(k6_yellow_6(sK4),sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_45])])).

fof(f213,plain,
    ( spl12_24
  <=> r2_hidden(sK7(sK4),k6_yellow_6(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f297,plain,
    ( ~ r2_hidden(k6_yellow_6(sK4),sK7(sK4))
    | ~ spl12_24 ),
    inference(resolution,[],[f214,f100])).

fof(f214,plain,
    ( r2_hidden(sK7(sK4),k6_yellow_6(sK4))
    | ~ spl12_24 ),
    inference(avatar_component_clause,[],[f213])).

fof(f312,plain,
    ( spl12_42
    | ~ spl12_24 ),
    inference(avatar_split_clause,[],[f296,f213,f310])).

fof(f310,plain,
    ( spl12_42
  <=> m1_subset_1(sK7(sK4),k6_yellow_6(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_42])])).

fof(f296,plain,
    ( m1_subset_1(sK7(sK4),k6_yellow_6(sK4))
    | ~ spl12_24 ),
    inference(resolution,[],[f214,f101])).

fof(f305,plain,
    ( ~ spl12_41
    | ~ spl12_24 ),
    inference(avatar_split_clause,[],[f298,f213,f303])).

fof(f303,plain,
    ( spl12_41
  <=> ~ v1_xboole_0(k6_yellow_6(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_41])])).

fof(f298,plain,
    ( ~ v1_xboole_0(k6_yellow_6(sK4))
    | ~ spl12_24 ),
    inference(resolution,[],[f214,f104])).

fof(f291,plain,
    ( spl12_18
    | spl12_39 ),
    inference(avatar_split_clause,[],[f285,f270,f175])).

fof(f270,plain,
    ( spl12_39
  <=> ~ v7_waybel_0(sK2(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_39])])).

fof(f285,plain,
    ( sP0(sK4)
    | ~ spl12_39 ),
    inference(resolution,[],[f271,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v7_waybel_0(sK2(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f271,plain,
    ( ~ v7_waybel_0(sK2(sK4))
    | ~ spl12_39 ),
    inference(avatar_component_clause,[],[f270])).

fof(f287,plain,
    ( spl12_19
    | spl12_39 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl12_19
    | ~ spl12_39 ),
    inference(subsumption_resolution,[],[f285,f173])).

fof(f284,plain,
    ( spl12_19
    | spl12_37 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | ~ spl12_19
    | ~ spl12_37 ),
    inference(subsumption_resolution,[],[f282,f173])).

fof(f282,plain,
    ( sP0(sK4)
    | ~ spl12_37 ),
    inference(resolution,[],[f265,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v4_orders_2(sK2(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f265,plain,
    ( ~ v4_orders_2(sK2(sK4))
    | ~ spl12_37 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl12_37
  <=> ~ v4_orders_2(sK2(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_37])])).

fof(f281,plain,
    ( spl12_19
    | spl12_33 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | ~ spl12_19
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f279,f173])).

fof(f279,plain,
    ( sP0(sK4)
    | ~ spl12_33 ),
    inference(resolution,[],[f253,f76])).

fof(f76,plain,(
    ! [X0] :
      ( l1_waybel_0(sK2(X0),X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f253,plain,
    ( ~ l1_waybel_0(sK2(sK4),sK4)
    | ~ spl12_33 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl12_33
  <=> ~ l1_waybel_0(sK2(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_33])])).

fof(f278,plain,
    ( spl12_34
    | ~ spl12_37
    | ~ spl12_39
    | ~ spl12_33
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_16
    | spl12_31 ),
    inference(avatar_split_clause,[],[f277,f246,f169,f127,f120,f113,f252,f270,f264,f258])).

fof(f113,plain,
    ( spl12_1
  <=> ~ v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f120,plain,
    ( spl12_2
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f127,plain,
    ( spl12_4
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f169,plain,
    ( spl12_16
  <=> v1_compts_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f277,plain,
    ( ~ l1_waybel_0(sK2(sK4),sK4)
    | ~ v7_waybel_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | v2_struct_0(sK2(sK4))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_16
    | ~ spl12_31 ),
    inference(subsumption_resolution,[],[f276,f114])).

fof(f114,plain,
    ( ~ v2_struct_0(sK4)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f276,plain,
    ( ~ l1_waybel_0(sK2(sK4),sK4)
    | ~ v7_waybel_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | v2_struct_0(sK2(sK4))
    | v2_struct_0(sK4)
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_16
    | ~ spl12_31 ),
    inference(subsumption_resolution,[],[f275,f121])).

fof(f121,plain,
    ( v2_pre_topc(sK4)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f275,plain,
    ( ~ l1_waybel_0(sK2(sK4),sK4)
    | ~ v7_waybel_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | v2_struct_0(sK2(sK4))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_4
    | ~ spl12_16
    | ~ spl12_31 ),
    inference(subsumption_resolution,[],[f274,f128])).

fof(f128,plain,
    ( l1_pre_topc(sK4)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f127])).

fof(f274,plain,
    ( ~ l1_waybel_0(sK2(sK4),sK4)
    | ~ v7_waybel_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | v2_struct_0(sK2(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_16
    | ~ spl12_31 ),
    inference(subsumption_resolution,[],[f273,f170])).

fof(f170,plain,
    ( v1_compts_1(sK4)
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f169])).

fof(f273,plain,
    ( ~ l1_waybel_0(sK2(sK4),sK4)
    | ~ v7_waybel_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | v2_struct_0(sK2(sK4))
    | ~ v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_31 ),
    inference(resolution,[],[f247,f90])).

fof(f90,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t35_yellow19.p',l37_yellow19)).

fof(f272,plain,
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
    inference(avatar_split_clause,[],[f241,f172,f169,f127,f120,f113,f270,f264,f258,f252,f246])).

fof(f241,plain,
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
    inference(subsumption_resolution,[],[f240,f173])).

fof(f240,plain,
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
    inference(resolution,[],[f239,f77])).

fof(f77,plain,(
    ! [X2,X0] :
      ( ~ r3_waybel_9(X0,sK2(X0),X2)
      | sP0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f239,plain,
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
    inference(subsumption_resolution,[],[f238,f114])).

fof(f238,plain,
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
    inference(subsumption_resolution,[],[f237,f121])).

fof(f237,plain,
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
    inference(subsumption_resolution,[],[f236,f128])).

fof(f236,plain,
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
    inference(resolution,[],[f91,f170])).

fof(f91,plain,(
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

fof(f234,plain,
    ( spl12_16
    | spl12_20
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f216,f127,f120,f113,f196,f169])).

fof(f216,plain,
    ( sP1(sK4)
    | v1_compts_1(sK4)
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f189,f114])).

fof(f189,plain,
    ( sP1(sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f188,f128])).

fof(f188,plain,
    ( sP1(sK4)
    | ~ l1_pre_topc(sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_2 ),
    inference(resolution,[],[f98,f121])).

fof(f98,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t35_yellow19.p',l38_yellow19)).

fof(f233,plain,
    ( ~ spl12_4
    | spl12_27 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl12_4
    | ~ spl12_27 ),
    inference(subsumption_resolution,[],[f230,f128])).

fof(f230,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ spl12_27 ),
    inference(resolution,[],[f222,f86])).

fof(f86,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t35_yellow19.p',dt_l1_pre_topc)).

fof(f222,plain,
    ( ~ l1_struct_0(sK4)
    | ~ spl12_27 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl12_27
  <=> ~ l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_27])])).

fof(f229,plain,
    ( ~ spl12_27
    | spl12_28
    | ~ spl12_22 ),
    inference(avatar_split_clause,[],[f208,f205,f227,f221])).

fof(f227,plain,
    ( spl12_28
  <=> l1_orders_2(sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).

fof(f208,plain,
    ( l1_orders_2(sK7(sK4))
    | ~ l1_struct_0(sK4)
    | ~ spl12_22 ),
    inference(resolution,[],[f206,f88])).

fof(f88,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t35_yellow19.p',dt_l1_waybel_0)).

fof(f215,plain,
    ( spl12_24
    | ~ spl12_20 ),
    inference(avatar_split_clause,[],[f199,f196,f213])).

fof(f199,plain,
    ( r2_hidden(sK7(sK4),k6_yellow_6(sK4))
    | ~ spl12_20 ),
    inference(resolution,[],[f197,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | r2_hidden(sK7(X0),k6_yellow_6(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f207,plain,
    ( spl12_22
    | ~ spl12_20 ),
    inference(avatar_split_clause,[],[f200,f196,f205])).

fof(f200,plain,
    ( l1_waybel_0(sK7(sK4),sK4)
    | ~ spl12_20 ),
    inference(resolution,[],[f197,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | l1_waybel_0(sK7(X0),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f198,plain,
    ( spl12_20
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | spl12_17 ),
    inference(avatar_split_clause,[],[f191,f166,f127,f120,f113,f196])).

fof(f166,plain,
    ( spl12_17
  <=> ~ v1_compts_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).

fof(f191,plain,
    ( sP1(sK4)
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_17 ),
    inference(subsumption_resolution,[],[f190,f114])).

fof(f190,plain,
    ( sP1(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_17 ),
    inference(subsumption_resolution,[],[f189,f167])).

fof(f167,plain,
    ( ~ v1_compts_1(sK4)
    | ~ spl12_17 ),
    inference(avatar_component_clause,[],[f166])).

fof(f178,plain,
    ( ~ spl12_17
    | ~ spl12_19 ),
    inference(avatar_split_clause,[],[f82,f172,f166])).

fof(f82,plain,
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
             => ? [X2] :
                  ( r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
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
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t35_yellow19.p',t35_yellow19)).

fof(f177,plain,
    ( spl12_16
    | spl12_18 ),
    inference(avatar_split_clause,[],[f81,f175,f169])).

fof(f81,plain,
    ( sP0(sK4)
    | v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f164,plain,(
    spl12_14 ),
    inference(avatar_split_clause,[],[f84,f162])).

fof(f162,plain,
    ( spl12_14
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f84,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/yellow19__t35_yellow19.p',d2_xboole_0)).

fof(f157,plain,(
    spl12_12 ),
    inference(avatar_split_clause,[],[f108,f155])).

fof(f155,plain,
    ( spl12_12
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f108,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f83,f84])).

fof(f83,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t35_yellow19.p',dt_o_0_0_xboole_0)).

fof(f150,plain,(
    spl12_10 ),
    inference(avatar_split_clause,[],[f107,f148])).

fof(f148,plain,
    ( spl12_10
  <=> l1_struct_0(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f107,plain,(
    l1_struct_0(sK11) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    l1_struct_0(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f16,f69])).

fof(f69,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK11) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t35_yellow19.p',existence_l1_struct_0)).

fof(f143,plain,(
    spl12_8 ),
    inference(avatar_split_clause,[],[f106,f141])).

fof(f141,plain,
    ( spl12_8
  <=> l1_pre_topc(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f106,plain,(
    l1_pre_topc(sK10) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    l1_pre_topc(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f15,f67])).

fof(f67,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK10) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t35_yellow19.p',existence_l1_pre_topc)).

fof(f136,plain,(
    spl12_6 ),
    inference(avatar_split_clause,[],[f105,f134])).

fof(f134,plain,
    ( spl12_6
  <=> l1_orders_2(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f105,plain,(
    l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    l1_orders_2(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f14,f65])).

fof(f65,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK9) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t35_yellow19.p',existence_l1_orders_2)).

fof(f129,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f80,f127])).

fof(f80,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f122,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f79,f120])).

fof(f79,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f115,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f78,f113])).

fof(f78,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
