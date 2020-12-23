%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 980 expanded)
%              Number of leaves         :   35 ( 356 expanded)
%              Depth                    :   21
%              Number of atoms          : 1224 (14418 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f371,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f124,f129,f134,f139,f144,f148,f264,f267,f270,f280,f299,f301,f365,f370])).

fof(f370,plain,
    ( spl14_2
    | ~ spl14_4
    | ~ spl14_17
    | ~ spl14_20 ),
    inference(avatar_contradiction_clause,[],[f369])).

fof(f369,plain,
    ( $false
    | spl14_2
    | ~ spl14_4
    | ~ spl14_17
    | ~ spl14_20 ),
    inference(subsumption_resolution,[],[f368,f113])).

fof(f113,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl14_4
  <=> m1_subset_1(sK9,u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f368,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | spl14_2
    | ~ spl14_17
    | ~ spl14_20 ),
    inference(subsumption_resolution,[],[f367,f278])).

fof(f278,plain,
    ( sP0(sK7,sK6)
    | ~ spl14_17 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl14_17
  <=> sP0(sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).

fof(f367,plain,
    ( ~ sP0(sK7,sK6)
    | ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | spl14_2
    | ~ spl14_20 ),
    inference(subsumption_resolution,[],[f366,f103])).

fof(f103,plain,
    ( ~ r2_hidden(sK9,sK7)
    | spl14_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl14_2
  <=> r2_hidden(sK9,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f366,plain,
    ( r2_hidden(sK9,sK7)
    | ~ sP0(sK7,sK6)
    | ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ spl14_20 ),
    inference(resolution,[],[f296,f229])).

fof(f229,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | r2_hidden(X0,X2)
      | ~ sP0(X2,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | r2_hidden(X0,X2)
      | ~ sP0(X2,X1)
      | ~ sP4(X0,X1,X2)
      | ~ sP4(X0,X1,X2) ) ),
    inference(resolution,[],[f225,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X1,sK13(X0,X1,X2),X2)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_waybel_9(X1,X3,X0)
            | ~ r1_waybel_0(X1,X3,X2)
            | ~ l1_waybel_0(X3,X1)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) ) )
      & ( ( r3_waybel_9(X1,sK13(X0,X1,X2),X0)
          & r1_waybel_0(X1,sK13(X0,X1,X2),X2)
          & l1_waybel_0(sK13(X0,X1,X2),X1)
          & v7_waybel_0(sK13(X0,X1,X2))
          & v4_orders_2(sK13(X0,X1,X2))
          & ~ v2_struct_0(sK13(X0,X1,X2)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X1,X4,X0)
          & r1_waybel_0(X1,X4,X2)
          & l1_waybel_0(X4,X1)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r3_waybel_9(X1,sK13(X0,X1,X2),X0)
        & r1_waybel_0(X1,sK13(X0,X1,X2),X2)
        & l1_waybel_0(sK13(X0,X1,X2),X1)
        & v7_waybel_0(sK13(X0,X1,X2))
        & v4_orders_2(sK13(X0,X1,X2))
        & ~ v2_struct_0(sK13(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_waybel_9(X1,X3,X0)
            | ~ r1_waybel_0(X1,X3,X2)
            | ~ l1_waybel_0(X3,X1)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) ) )
      & ( ? [X4] :
            ( r3_waybel_9(X1,X4,X0)
            & r1_waybel_0(X1,X4,X2)
            & l1_waybel_0(X4,X1)
            & v7_waybel_0(X4)
            & v4_orders_2(X4)
            & ~ v2_struct_0(X4) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ( sP4(X2,X0,X1)
        | ! [X3] :
            ( ~ r3_waybel_9(X0,X3,X2)
            | ~ r1_waybel_0(X0,X3,X1)
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) ) )
      & ( ? [X3] :
            ( r3_waybel_9(X0,X3,X2)
            & r1_waybel_0(X0,X3,X1)
            & l1_waybel_0(X3,X0)
            & v7_waybel_0(X3)
            & v4_orders_2(X3)
            & ~ v2_struct_0(X3) )
        | ~ sP4(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0,X1)
    <=> ? [X3] :
          ( r3_waybel_9(X0,X3,X2)
          & r1_waybel_0(X0,X3,X1)
          & l1_waybel_0(X3,X0)
          & v7_waybel_0(X3)
          & v4_orders_2(X3)
          & ~ v2_struct_0(X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f225,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r1_waybel_0(X5,sK13(X3,X5,X6),X4)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | r2_hidden(X3,X4)
      | ~ sP0(X4,X5)
      | ~ sP4(X3,X5,X6) ) ),
    inference(subsumption_resolution,[],[f224,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK13(X0,X1,X2))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f224,plain,(
    ! [X6,X4,X5,X3] :
      ( r2_hidden(X3,X4)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | ~ r1_waybel_0(X5,sK13(X3,X5,X6),X4)
      | v2_struct_0(sK13(X3,X5,X6))
      | ~ sP0(X4,X5)
      | ~ sP4(X3,X5,X6) ) ),
    inference(subsumption_resolution,[],[f223,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(sK13(X0,X1,X2))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f223,plain,(
    ! [X6,X4,X5,X3] :
      ( r2_hidden(X3,X4)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | ~ r1_waybel_0(X5,sK13(X3,X5,X6),X4)
      | ~ v4_orders_2(sK13(X3,X5,X6))
      | v2_struct_0(sK13(X3,X5,X6))
      | ~ sP0(X4,X5)
      | ~ sP4(X3,X5,X6) ) ),
    inference(subsumption_resolution,[],[f222,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(sK13(X0,X1,X2))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f222,plain,(
    ! [X6,X4,X5,X3] :
      ( r2_hidden(X3,X4)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | ~ r1_waybel_0(X5,sK13(X3,X5,X6),X4)
      | ~ v7_waybel_0(sK13(X3,X5,X6))
      | ~ v4_orders_2(sK13(X3,X5,X6))
      | v2_struct_0(sK13(X3,X5,X6))
      | ~ sP0(X4,X5)
      | ~ sP4(X3,X5,X6) ) ),
    inference(subsumption_resolution,[],[f216,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(sK13(X0,X1,X2),X1)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f216,plain,(
    ! [X6,X4,X5,X3] :
      ( r2_hidden(X3,X4)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | ~ r1_waybel_0(X5,sK13(X3,X5,X6),X4)
      | ~ l1_waybel_0(sK13(X3,X5,X6),X5)
      | ~ v7_waybel_0(sK13(X3,X5,X6))
      | ~ v4_orders_2(sK13(X3,X5,X6))
      | v2_struct_0(sK13(X3,X5,X6))
      | ~ sP0(X4,X5)
      | ~ sP4(X3,X5,X6) ) ),
    inference(resolution,[],[f65,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X1,sK13(X0,X1,X2),X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f65,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r3_waybel_9(X1,X4,X5)
      | r2_hidden(X5,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_waybel_0(X1,X4,X0)
      | ~ l1_waybel_0(X4,X1)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X0)
          & r3_waybel_9(X1,sK10(X0,X1),sK11(X0,X1))
          & m1_subset_1(sK11(X0,X1),u1_struct_0(X1))
          & r1_waybel_0(X1,sK10(X0,X1),X0)
          & l1_waybel_0(sK10(X0,X1),X1)
          & v7_waybel_0(sK10(X0,X1))
          & v4_orders_2(sK10(X0,X1))
          & ~ v2_struct_0(sK10(X0,X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r3_waybel_9(X1,X4,X5)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r1_waybel_0(X1,X4,X0)
            | ~ l1_waybel_0(X4,X1)
            | ~ v7_waybel_0(X4)
            | ~ v4_orders_2(X4)
            | v2_struct_0(X4) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f33,f35,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X0)
              & r3_waybel_9(X1,X2,X3)
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & r1_waybel_0(X1,X2,X0)
          & l1_waybel_0(X2,X1)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X0)
            & r3_waybel_9(X1,sK10(X0,X1),X3)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & r1_waybel_0(X1,sK10(X0,X1),X0)
        & l1_waybel_0(sK10(X0,X1),X1)
        & v7_waybel_0(sK10(X0,X1))
        & v4_orders_2(sK10(X0,X1))
        & ~ v2_struct_0(sK10(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r3_waybel_9(X1,sK10(X0,X1),X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_hidden(sK11(X0,X1),X0)
        & r3_waybel_9(X1,sK10(X0,X1),sK11(X0,X1))
        & m1_subset_1(sK11(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X0)
                & r3_waybel_9(X1,X2,X3)
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & r1_waybel_0(X1,X2,X0)
            & l1_waybel_0(X2,X1)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r3_waybel_9(X1,X4,X5)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r1_waybel_0(X1,X4,X0)
            | ~ l1_waybel_0(X4,X1)
            | ~ v7_waybel_0(X4)
            | ~ v4_orders_2(X4)
            | v2_struct_0(X4) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r3_waybel_9(X0,X2,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & r1_waybel_0(X0,X2,X1)
            & l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( r2_hidden(X3,X1)
                | ~ r3_waybel_9(X0,X2,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ r1_waybel_0(X0,X2,X1)
            | ~ l1_waybel_0(X2,X0)
            | ~ v7_waybel_0(X2)
            | ~ v4_orders_2(X2)
            | v2_struct_0(X2) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r3_waybel_9(X0,X2,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_waybel_0(X0,X2,X1)
          | ~ l1_waybel_0(X2,X0)
          | ~ v7_waybel_0(X2)
          | ~ v4_orders_2(X2)
          | v2_struct_0(X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f296,plain,
    ( sP4(sK9,sK6,sK7)
    | ~ spl14_20 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl14_20
  <=> sP4(sK9,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_20])])).

fof(f365,plain,
    ( ~ spl14_3
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_9
    | spl14_10
    | spl14_19 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | ~ spl14_3
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_9
    | spl14_10
    | spl14_19 ),
    inference(subsumption_resolution,[],[f363,f118])).

fof(f118,plain,
    ( r2_hidden(sK7,sK8)
    | ~ spl14_5 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl14_5
  <=> r2_hidden(sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f363,plain,
    ( ~ r2_hidden(sK7,sK8)
    | ~ spl14_3
    | ~ spl14_6
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_9
    | spl14_10
    | spl14_19 ),
    inference(resolution,[],[f362,f292])).

fof(f292,plain,
    ( ~ sP2(sK9,sK6,sK7)
    | spl14_19 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl14_19
  <=> sP2(sK9,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).

fof(f362,plain,
    ( ! [X0] :
        ( sP2(sK9,sK6,X0)
        | ~ r2_hidden(X0,sK8) )
    | ~ spl14_3
    | ~ spl14_6
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_9
    | spl14_10 ),
    inference(resolution,[],[f332,f108])).

fof(f108,plain,
    ( r1_waybel_7(sK6,sK8,sK9)
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl14_3
  <=> r1_waybel_7(sK6,sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f332,plain,
    ( ! [X2,X1] :
        ( ~ r1_waybel_7(sK6,sK8,X1)
        | ~ r2_hidden(X2,sK8)
        | sP2(X1,sK6,X2) )
    | ~ spl14_6
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_9
    | spl14_10 ),
    inference(subsumption_resolution,[],[f331,f143])).

fof(f143,plain,
    ( ~ v1_xboole_0(sK8)
    | spl14_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl14_10
  <=> v1_xboole_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f331,plain,
    ( ! [X2,X1] :
        ( ~ r1_waybel_7(sK6,sK8,X1)
        | ~ r2_hidden(X2,sK8)
        | sP2(X1,sK6,X2)
        | v1_xboole_0(sK8) )
    | ~ spl14_6
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_9 ),
    inference(subsumption_resolution,[],[f330,f138])).

fof(f138,plain,
    ( v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
    | ~ spl14_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl14_9
  <=> v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).

fof(f330,plain,
    ( ! [X2,X1] :
        ( ~ r1_waybel_7(sK6,sK8,X1)
        | ~ r2_hidden(X2,sK8)
        | sP2(X1,sK6,X2)
        | ~ v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
        | v1_xboole_0(sK8) )
    | ~ spl14_6
    | ~ spl14_7
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f329,f133])).

fof(f133,plain,
    ( v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl14_8
  <=> v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f329,plain,
    ( ! [X2,X1] :
        ( ~ r1_waybel_7(sK6,sK8,X1)
        | ~ r2_hidden(X2,sK8)
        | sP2(X1,sK6,X2)
        | ~ v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
        | ~ v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
        | v1_xboole_0(sK8) )
    | ~ spl14_6
    | ~ spl14_7 ),
    inference(subsumption_resolution,[],[f320,f128])).

fof(f128,plain,
    ( v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ spl14_7 ),
    inference(avatar_component_clause,[],[f126])).

% (11017)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
fof(f126,plain,
    ( spl14_7
  <=> v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).

fof(f320,plain,
    ( ! [X2,X1] :
        ( ~ r1_waybel_7(sK6,sK8,X1)
        | ~ r2_hidden(X2,sK8)
        | sP2(X1,sK6,X2)
        | ~ v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
        | ~ v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
        | ~ v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
        | v1_xboole_0(sK8) )
    | ~ spl14_6 ),
    inference(resolution,[],[f123,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
      | ~ r1_waybel_7(X1,X3,X0)
      | ~ r2_hidden(X2,X3)
      | sP2(X0,X1,X2)
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_waybel_7(X1,X3,X0)
            | ~ r2_hidden(X2,X3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
            | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
            | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
            | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
            | v1_xboole_0(X3) ) )
      & ( ( r1_waybel_7(X1,sK12(X0,X1,X2),X0)
          & r2_hidden(X2,sK12(X0,X1,X2))
          & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
          & v13_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1)))
          & v2_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1)))
          & v1_subset_1(sK12(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
          & ~ v1_xboole_0(sK12(X0,X1,X2)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_waybel_7(X1,X4,X0)
          & r2_hidden(X2,X4)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
          & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
          & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
          & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
          & ~ v1_xboole_0(X4) )
     => ( r1_waybel_7(X1,sK12(X0,X1,X2),X0)
        & r2_hidden(X2,sK12(X0,X1,X2))
        & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
        & v13_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1)))
        & v2_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1)))
        & v1_subset_1(sK12(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
        & ~ v1_xboole_0(sK12(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_waybel_7(X1,X3,X0)
            | ~ r2_hidden(X2,X3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
            | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
            | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1)))
            | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
            | v1_xboole_0(X3) ) )
      & ( ? [X4] :
            ( r1_waybel_7(X1,X4,X0)
            & r2_hidden(X2,X4)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
            & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
            & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
            & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
            & ~ v1_xboole_0(X4) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ! [X3] :
            ( ~ r1_waybel_7(X0,X3,X2)
            | ~ r2_hidden(X1,X3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
            | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
            | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            | v1_xboole_0(X3) ) )
      & ( ? [X3] :
            ( r1_waybel_7(X0,X3,X2)
            & r2_hidden(X1,X3)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X3) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ? [X3] :
          ( r1_waybel_7(X0,X3,X2)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f123,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl14_6
  <=> m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f301,plain,
    ( ~ spl14_4
    | spl14_18 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | ~ spl14_4
    | spl14_18 ),
    inference(subsumption_resolution,[],[f289,f283])).

fof(f283,plain,
    ( sP3(sK7,sK6,sK9)
    | ~ spl14_4 ),
    inference(resolution,[],[f113,f169])).

fof(f169,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | sP3(sK7,sK6,X0) ) ),
    inference(subsumption_resolution,[],[f168,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ( ~ r2_hidden(sK9,sK7)
        & r1_waybel_7(sK6,sK8,sK9)
        & m1_subset_1(sK9,u1_struct_0(sK6))
        & r2_hidden(sK7,sK8)
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
        & v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
        & v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
        & v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
        & ~ v1_xboole_0(sK8) )
      | ~ v4_pre_topc(sK7,sK6) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r2_hidden(X5,sK7)
              | ~ r1_waybel_7(sK6,X4,X5)
              | ~ m1_subset_1(X5,u1_struct_0(sK6)) )
          | ~ r2_hidden(sK7,X4)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
          | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
          | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
          | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
          | v1_xboole_0(X4) )
      | v4_pre_topc(sK7,sK6) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f25,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_waybel_7(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  & ~ v1_xboole_0(X2) )
              | ~ v4_pre_topc(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_waybel_7(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X4)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  | v1_xboole_0(X4) )
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r1_waybel_7(sK6,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(sK6)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
                & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,sK6) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r1_waybel_7(sK6,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(sK6)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
                | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,sK6) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X3,X1)
                  & r1_waybel_7(sK6,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(sK6)) )
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
              & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
              & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
              & ~ v1_xboole_0(X2) )
          | ~ v4_pre_topc(X1,sK6) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X1)
                  | ~ r1_waybel_7(sK6,X4,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(sK6)) )
              | ~ r2_hidden(X1,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
              | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
              | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
              | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
              | v1_xboole_0(X4) )
          | v4_pre_topc(X1,sK6) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
   => ( ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,sK7)
                & r1_waybel_7(sK6,X2,X3)
                & m1_subset_1(X3,u1_struct_0(sK6)) )
            & r2_hidden(sK7,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
            & ~ v1_xboole_0(X2) )
        | ~ v4_pre_topc(sK7,sK6) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,sK7)
                | ~ r1_waybel_7(sK6,X4,X5)
                | ~ m1_subset_1(X5,u1_struct_0(sK6)) )
            | ~ r2_hidden(sK7,X4)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
            | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
            | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
            | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
            | v1_xboole_0(X4) )
        | v4_pre_topc(sK7,sK6) )
      & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_hidden(X3,sK7)
            & r1_waybel_7(sK6,X2,X3)
            & m1_subset_1(X3,u1_struct_0(sK6)) )
        & r2_hidden(sK7,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
        & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
        & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ~ r2_hidden(X3,sK7)
          & r1_waybel_7(sK6,sK8,X3)
          & m1_subset_1(X3,u1_struct_0(sK6)) )
      & r2_hidden(sK7,sK8)
      & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
      & v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
      & v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
      & v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
      & ~ v1_xboole_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ~ r2_hidden(X3,sK7)
        & r1_waybel_7(sK6,sK8,X3)
        & m1_subset_1(X3,u1_struct_0(sK6)) )
   => ( ~ r2_hidden(sK9,sK7)
      & r1_waybel_7(sK6,sK8,sK9)
      & m1_subset_1(sK9,u1_struct_0(sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r1_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r1_waybel_7(X0,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r1_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r1_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X2) )
                 => ( r2_hidden(X1,X2)
                   => ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r1_waybel_7(X0,X2,X3)
                         => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  & ~ v1_xboole_0(X2) )
               => ( r2_hidden(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_waybel_7(X0,X2,X3)
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow19)).

fof(f168,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | sP3(sK7,sK6,X0)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f167,f50])).

fof(f50,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f167,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | sP3(sK7,sK6,X0)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f165,f51])).

fof(f51,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f165,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | sP3(sK7,sK6,X0)
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6) ) ),
    inference(resolution,[],[f85,f52])).

fof(f52,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP3(X1,X0,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP3(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f11,f18,f17])).

fof(f18,plain,(
    ! [X1,X0,X2] :
      ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
      <=> sP2(X2,X0,X1) )
      | ~ sP3(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow19)).

fof(f289,plain,
    ( ~ sP3(sK7,sK6,sK9)
    | spl14_18 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl14_18
  <=> sP3(sK7,sK6,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).

fof(f299,plain,
    ( ~ spl14_18
    | ~ spl14_19
    | spl14_20
    | ~ spl14_4 ),
    inference(avatar_split_clause,[],[f285,f111,f295,f291,f287])).

fof(f285,plain,
    ( sP4(sK9,sK6,sK7)
    | ~ sP2(sK9,sK6,sK7)
    | ~ sP3(sK7,sK6,sK9)
    | ~ spl14_4 ),
    inference(resolution,[],[f282,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X2,X1,X0)
      | sP4(X0,X1,X2)
      | ~ sP2(X0,X1,X2)
      | ~ sP3(X2,X1,X0) ) ),
    inference(resolution,[],[f86,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X1,X0))
      | ~ sP2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X2,k2_pre_topc(X1,X0))
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | ~ r2_hidden(X2,k2_pre_topc(X1,X0)) ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
          | ~ sP2(X2,X0,X1) )
        & ( sP2(X2,X0,X1)
          | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
      | ~ sP3(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X1,X0))
      | sP4(X2,X1,X0)
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X2,k2_pre_topc(X1,X0))
          | ~ sP4(X2,X1,X0) )
        & ( sP4(X2,X1,X0)
          | ~ r2_hidden(X2,k2_pre_topc(X1,X0)) ) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X0,X2] :
      ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
          | ~ sP4(X2,X0,X1) )
        & ( sP4(X2,X0,X1)
          | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
      | ~ sP5(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X1,X0,X2] :
      ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
      <=> sP4(X2,X0,X1) )
      | ~ sP5(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f282,plain,
    ( sP5(sK7,sK6,sK9)
    | ~ spl14_4 ),
    inference(resolution,[],[f113,f175])).

fof(f175,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | sP5(sK7,sK6,X0) ) ),
    inference(subsumption_resolution,[],[f174,f49])).

fof(f174,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | sP5(sK7,sK6,X0)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f173,f50])).

fof(f173,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | sP5(sK7,sK6,X0)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f171,f51])).

fof(f171,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
      | sP5(sK7,sK6,X0)
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6) ) ),
    inference(resolution,[],[f95,f52])).

% (11017)Refutation not found, incomplete strategy% (11017)------------------------------
% (11017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11017)Termination reason: Refutation not found, incomplete strategy

% (11017)Memory used [KB]: 895
% (11017)Time elapsed: 0.083 s
% (11017)------------------------------
% (11017)------------------------------
fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP5(X1,X0,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP5(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f13,f21,f20])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow19)).

fof(f280,plain,
    ( spl14_17
    | ~ spl14_1 ),
    inference(avatar_split_clause,[],[f162,f97,f276])).

fof(f97,plain,
    ( spl14_1
  <=> v4_pre_topc(sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f162,plain,
    ( ~ v4_pre_topc(sK7,sK6)
    | sP0(sK7,sK6) ),
    inference(resolution,[],[f160,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v4_pre_topc(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v4_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v4_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v4_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f160,plain,(
    sP1(sK6,sK7) ),
    inference(subsumption_resolution,[],[f159,f49])).

fof(f159,plain,
    ( sP1(sK6,sK7)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f158,f50])).

fof(f158,plain,
    ( sP1(sK6,sK7)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f157,f51])).

fof(f157,plain,
    ( sP1(sK6,sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f74,f52])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f9,f15,f14])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r3_waybel_9(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r3_waybel_9(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( r1_waybel_0(X0,X2,X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r3_waybel_9(X0,X2,X3)
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow19)).

fof(f270,plain,
    ( spl14_1
    | ~ spl14_15 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | spl14_1
    | ~ spl14_15 ),
    inference(subsumption_resolution,[],[f268,f163])).

fof(f163,plain,
    ( ~ sP0(sK7,sK6)
    | spl14_1 ),
    inference(subsumption_resolution,[],[f161,f99])).

fof(f99,plain,
    ( ~ v4_pre_topc(sK7,sK6)
    | spl14_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f161,plain,
    ( ~ sP0(sK7,sK6)
    | v4_pre_topc(sK7,sK6) ),
    inference(resolution,[],[f160,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f268,plain,
    ( sP0(sK7,sK6)
    | ~ spl14_15 ),
    inference(resolution,[],[f263,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK11(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f263,plain,
    ( r2_hidden(sK11(sK7,sK6),sK7)
    | ~ spl14_15 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl14_15
  <=> r2_hidden(sK11(sK7,sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_15])])).

fof(f267,plain,
    ( spl14_1
    | spl14_14 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | spl14_1
    | spl14_14 ),
    inference(subsumption_resolution,[],[f265,f163])).

fof(f265,plain,
    ( sP0(sK7,sK6)
    | spl14_14 ),
    inference(resolution,[],[f259,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK11(X0,X1),u1_struct_0(X1))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f259,plain,
    ( ~ m1_subset_1(sK11(sK7,sK6),u1_struct_0(sK6))
    | spl14_14 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl14_14
  <=> m1_subset_1(sK11(sK7,sK6),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f264,plain,
    ( ~ spl14_14
    | spl14_15
    | spl14_1
    | ~ spl14_11 ),
    inference(avatar_split_clause,[],[f255,f146,f97,f261,f257])).

fof(f146,plain,
    ( spl14_11
  <=> ! [X5,X4] :
        ( r2_hidden(X5,sK7)
        | v1_xboole_0(X4)
        | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
        | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
        | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
        | ~ r2_hidden(sK7,X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK6))
        | ~ r1_waybel_7(sK6,X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).

fof(f255,plain,
    ( r2_hidden(sK11(sK7,sK6),sK7)
    | ~ m1_subset_1(sK11(sK7,sK6),u1_struct_0(sK6))
    | spl14_1
    | ~ spl14_11 ),
    inference(resolution,[],[f254,f195])).

fof(f195,plain,
    ( sP2(sK11(sK7,sK6),sK6,sK7)
    | spl14_1 ),
    inference(subsumption_resolution,[],[f194,f163])).

fof(f194,plain,
    ( sP0(sK7,sK6)
    | sP2(sK11(sK7,sK6),sK6,sK7) ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,
    ( sP0(sK7,sK6)
    | sP0(sK7,sK6)
    | sP2(sK11(sK7,sK6),sK6,sK7) ),
    inference(resolution,[],[f192,f179])).

fof(f179,plain,(
    ! [X0] :
      ( ~ sP4(sK11(X0,sK6),sK6,sK7)
      | sP0(X0,sK6)
      | sP2(sK11(X0,sK6),sK6,sK7) ) ),
    inference(subsumption_resolution,[],[f177,f170])).

fof(f170,plain,(
    ! [X0] :
      ( sP3(sK7,sK6,sK11(X0,sK6))
      | sP0(X0,sK6) ) ),
    inference(resolution,[],[f169,f71])).

fof(f177,plain,(
    ! [X0] :
      ( sP0(X0,sK6)
      | ~ sP4(sK11(X0,sK6),sK6,sK7)
      | sP2(sK11(X0,sK6),sK6,sK7)
      | ~ sP3(sK7,sK6,sK11(X0,sK6)) ) ),
    inference(resolution,[],[f176,f154])).

fof(f154,plain,(
    ! [X4,X5,X3] :
      ( ~ sP5(X5,X4,X3)
      | ~ sP4(X3,X4,X5)
      | sP2(X3,X4,X5)
      | ~ sP3(X5,X4,X3) ) ),
    inference(resolution,[],[f87,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X1,X0))
      | sP2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X1,X0))
      | ~ sP4(X2,X1,X0)
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f176,plain,(
    ! [X0] :
      ( sP5(sK7,sK6,sK11(X0,sK6))
      | sP0(X0,sK6) ) ),
    inference(resolution,[],[f175,f71])).

fof(f192,plain,(
    ! [X0,X1] :
      ( sP4(sK11(X0,X1),X1,X0)
      | sP0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( sP4(sK11(X0,X1),X1,X0)
      | sP0(X0,X1)
      | sP0(X0,X1) ) ),
    inference(resolution,[],[f186,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(X1,sK10(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_waybel_0(X1,sK10(X0,X1),X2)
      | sP4(sK11(X0,X1),X1,X2)
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f185,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK10(X0,X1))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( sP4(sK11(X0,X1),X1,X2)
      | ~ r1_waybel_0(X1,sK10(X0,X1),X2)
      | v2_struct_0(sK10(X0,X1))
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f184,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v4_orders_2(sK10(X0,X1))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( sP4(sK11(X0,X1),X1,X2)
      | ~ r1_waybel_0(X1,sK10(X0,X1),X2)
      | ~ v4_orders_2(sK10(X0,X1))
      | v2_struct_0(sK10(X0,X1))
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f183,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v7_waybel_0(sK10(X0,X1))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( sP4(sK11(X0,X1),X1,X2)
      | ~ r1_waybel_0(X1,sK10(X0,X1),X2)
      | ~ v7_waybel_0(sK10(X0,X1))
      | ~ v4_orders_2(sK10(X0,X1))
      | v2_struct_0(sK10(X0,X1))
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f181,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( l1_waybel_0(sK10(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( sP4(sK11(X0,X1),X1,X2)
      | ~ r1_waybel_0(X1,sK10(X0,X1),X2)
      | ~ l1_waybel_0(sK10(X0,X1),X1)
      | ~ v7_waybel_0(sK10(X0,X1))
      | ~ v4_orders_2(sK10(X0,X1))
      | v2_struct_0(sK10(X0,X1))
      | sP0(X0,X1) ) ),
    inference(resolution,[],[f94,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X1,sK10(X0,X1),sK11(X0,X1))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_waybel_9(X1,X3,X0)
      | sP4(X0,X1,X2)
      | ~ r1_waybel_0(X1,X3,X2)
      | ~ l1_waybel_0(X3,X1)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f254,plain,
    ( ! [X0] :
        ( ~ sP2(X0,sK6,sK7)
        | r2_hidden(X0,sK7)
        | ~ m1_subset_1(X0,u1_struct_0(sK6)) )
    | ~ spl14_11 ),
    inference(duplicate_literal_removal,[],[f253])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK6))
        | r2_hidden(X0,sK7)
        | ~ sP2(X0,sK6,sK7)
        | ~ sP2(X0,sK6,sK7) )
    | ~ spl14_11 ),
    inference(resolution,[],[f252,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK12(X0,X1,X2))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f252,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK7,sK12(X0,sK6,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | r2_hidden(X0,sK7)
        | ~ sP2(X0,sK6,X1) )
    | ~ spl14_11 ),
    inference(duplicate_literal_removal,[],[f251])).

fof(f251,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK7,sK12(X0,sK6,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | r2_hidden(X0,sK7)
        | ~ sP2(X0,sK6,X1)
        | ~ sP2(X0,sK6,X1) )
    | ~ spl14_11 ),
    inference(resolution,[],[f250,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_7(X1,sK12(X0,X1,X2),X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f250,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_waybel_7(sK6,sK12(X0,sK6,X1),X2)
        | ~ r2_hidden(sK7,sK12(X0,sK6,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK6))
        | r2_hidden(X2,sK7)
        | ~ sP2(X0,sK6,X1) )
    | ~ spl14_11 ),
    inference(subsumption_resolution,[],[f249,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v13_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1)))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f249,plain,
    ( ! [X2,X0,X1] :
        ( ~ v13_waybel_0(sK12(X0,sK6,X1),k3_yellow_1(k2_struct_0(sK6)))
        | r2_hidden(X2,sK7)
        | ~ r2_hidden(sK7,sK12(X0,sK6,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK6))
        | ~ r1_waybel_7(sK6,sK12(X0,sK6,X1),X2)
        | ~ sP2(X0,sK6,X1) )
    | ~ spl14_11 ),
    inference(subsumption_resolution,[],[f248,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1)))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f248,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_waybel_0(sK12(X0,sK6,X1),k3_yellow_1(k2_struct_0(sK6)))
        | ~ v13_waybel_0(sK12(X0,sK6,X1),k3_yellow_1(k2_struct_0(sK6)))
        | r2_hidden(X2,sK7)
        | ~ r2_hidden(sK7,sK12(X0,sK6,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK6))
        | ~ r1_waybel_7(sK6,sK12(X0,sK6,X1),X2)
        | ~ sP2(X0,sK6,X1) )
    | ~ spl14_11 ),
    inference(subsumption_resolution,[],[f247,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_subset_1(sK12(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f247,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_subset_1(sK12(X0,sK6,X1),u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
        | ~ v2_waybel_0(sK12(X0,sK6,X1),k3_yellow_1(k2_struct_0(sK6)))
        | ~ v13_waybel_0(sK12(X0,sK6,X1),k3_yellow_1(k2_struct_0(sK6)))
        | r2_hidden(X2,sK7)
        | ~ r2_hidden(sK7,sK12(X0,sK6,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK6))
        | ~ r1_waybel_7(sK6,sK12(X0,sK6,X1),X2)
        | ~ sP2(X0,sK6,X1) )
    | ~ spl14_11 ),
    inference(subsumption_resolution,[],[f246,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK12(X0,X1,X2))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f246,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(sK12(X0,sK6,X1))
        | ~ v1_subset_1(sK12(X0,sK6,X1),u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
        | ~ v2_waybel_0(sK12(X0,sK6,X1),k3_yellow_1(k2_struct_0(sK6)))
        | ~ v13_waybel_0(sK12(X0,sK6,X1),k3_yellow_1(k2_struct_0(sK6)))
        | r2_hidden(X2,sK7)
        | ~ r2_hidden(sK7,sK12(X0,sK6,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK6))
        | ~ r1_waybel_7(sK6,sK12(X0,sK6,X1),X2)
        | ~ sP2(X0,sK6,X1) )
    | ~ spl14_11 ),
    inference(resolution,[],[f147,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f147,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
        | v1_xboole_0(X4)
        | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
        | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
        | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
        | r2_hidden(X5,sK7)
        | ~ r2_hidden(sK7,X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK6))
        | ~ r1_waybel_7(sK6,X4,X5) )
    | ~ spl14_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f148,plain,
    ( spl14_1
    | spl14_11 ),
    inference(avatar_split_clause,[],[f53,f146,f97])).

fof(f53,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,sK7)
      | ~ r1_waybel_7(sK6,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK6))
      | ~ r2_hidden(sK7,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
      | v1_xboole_0(X4)
      | v4_pre_topc(sK7,sK6) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f144,plain,
    ( ~ spl14_1
    | ~ spl14_10 ),
    inference(avatar_split_clause,[],[f54,f141,f97])).

fof(f54,plain,
    ( ~ v1_xboole_0(sK8)
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f139,plain,
    ( ~ spl14_1
    | spl14_9 ),
    inference(avatar_split_clause,[],[f55,f136,f97])).

fof(f55,plain,
    ( v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f134,plain,
    ( ~ spl14_1
    | spl14_8 ),
    inference(avatar_split_clause,[],[f56,f131,f97])).

fof(f56,plain,
    ( v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f129,plain,
    ( ~ spl14_1
    | spl14_7 ),
    inference(avatar_split_clause,[],[f57,f126,f97])).

fof(f57,plain,
    ( v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f124,plain,
    ( ~ spl14_1
    | spl14_6 ),
    inference(avatar_split_clause,[],[f58,f121,f97])).

fof(f58,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f119,plain,
    ( ~ spl14_1
    | spl14_5 ),
    inference(avatar_split_clause,[],[f59,f116,f97])).

fof(f59,plain,
    ( r2_hidden(sK7,sK8)
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f114,plain,
    ( ~ spl14_1
    | spl14_4 ),
    inference(avatar_split_clause,[],[f60,f111,f97])).

fof(f60,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f109,plain,
    ( ~ spl14_1
    | spl14_3 ),
    inference(avatar_split_clause,[],[f61,f106,f97])).

fof(f61,plain,
    ( r1_waybel_7(sK6,sK8,sK9)
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f104,plain,
    ( ~ spl14_1
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f62,f101,f97])).

fof(f62,plain,
    ( ~ r2_hidden(sK9,sK7)
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (11014)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.47  % (11005)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.48  % (11008)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.48  % (11021)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.21/0.48  % (11001)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (11016)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.49  % (11008)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (11012)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.49  % (11016)Refutation not found, incomplete strategy% (11016)------------------------------
% 0.21/0.49  % (11016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11007)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.49  % (11009)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (11016)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (11016)Memory used [KB]: 5373
% 0.21/0.49  % (11016)Time elapsed: 0.009 s
% 0.21/0.49  % (11016)------------------------------
% 0.21/0.49  % (11016)------------------------------
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f371,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f124,f129,f134,f139,f144,f148,f264,f267,f270,f280,f299,f301,f365,f370])).
% 0.21/0.49  fof(f370,plain,(
% 0.21/0.49    spl14_2 | ~spl14_4 | ~spl14_17 | ~spl14_20),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f369])).
% 0.21/0.49  fof(f369,plain,(
% 0.21/0.49    $false | (spl14_2 | ~spl14_4 | ~spl14_17 | ~spl14_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f368,f113])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    m1_subset_1(sK9,u1_struct_0(sK6)) | ~spl14_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f111])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    spl14_4 <=> m1_subset_1(sK9,u1_struct_0(sK6))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).
% 0.21/0.49  fof(f368,plain,(
% 0.21/0.49    ~m1_subset_1(sK9,u1_struct_0(sK6)) | (spl14_2 | ~spl14_17 | ~spl14_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f367,f278])).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    sP0(sK7,sK6) | ~spl14_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f276])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    spl14_17 <=> sP0(sK7,sK6)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).
% 0.21/0.49  fof(f367,plain,(
% 0.21/0.49    ~sP0(sK7,sK6) | ~m1_subset_1(sK9,u1_struct_0(sK6)) | (spl14_2 | ~spl14_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f366,f103])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ~r2_hidden(sK9,sK7) | spl14_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl14_2 <=> r2_hidden(sK9,sK7)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 0.21/0.49  fof(f366,plain,(
% 0.21/0.49    r2_hidden(sK9,sK7) | ~sP0(sK7,sK6) | ~m1_subset_1(sK9,u1_struct_0(sK6)) | ~spl14_20),
% 0.21/0.49    inference(resolution,[],[f296,f229])).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | r2_hidden(X0,X2) | ~sP0(X2,X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f228])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | r2_hidden(X0,X2) | ~sP0(X2,X1) | ~sP4(X0,X1,X2) | ~sP4(X0,X1,X2)) )),
% 0.21/0.49    inference(resolution,[],[f225,f92])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_waybel_0(X1,sK13(X0,X1,X2),X2) | ~sP4(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ! [X3] : (~r3_waybel_9(X1,X3,X0) | ~r1_waybel_0(X1,X3,X2) | ~l1_waybel_0(X3,X1) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & ((r3_waybel_9(X1,sK13(X0,X1,X2),X0) & r1_waybel_0(X1,sK13(X0,X1,X2),X2) & l1_waybel_0(sK13(X0,X1,X2),X1) & v7_waybel_0(sK13(X0,X1,X2)) & v4_orders_2(sK13(X0,X1,X2)) & ~v2_struct_0(sK13(X0,X1,X2))) | ~sP4(X0,X1,X2)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f46,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X4] : (r3_waybel_9(X1,X4,X0) & r1_waybel_0(X1,X4,X2) & l1_waybel_0(X4,X1) & v7_waybel_0(X4) & v4_orders_2(X4) & ~v2_struct_0(X4)) => (r3_waybel_9(X1,sK13(X0,X1,X2),X0) & r1_waybel_0(X1,sK13(X0,X1,X2),X2) & l1_waybel_0(sK13(X0,X1,X2),X1) & v7_waybel_0(sK13(X0,X1,X2)) & v4_orders_2(sK13(X0,X1,X2)) & ~v2_struct_0(sK13(X0,X1,X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ! [X3] : (~r3_waybel_9(X1,X3,X0) | ~r1_waybel_0(X1,X3,X2) | ~l1_waybel_0(X3,X1) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & (? [X4] : (r3_waybel_9(X1,X4,X0) & r1_waybel_0(X1,X4,X2) & l1_waybel_0(X4,X1) & v7_waybel_0(X4) & v4_orders_2(X4) & ~v2_struct_0(X4)) | ~sP4(X0,X1,X2)))),
% 0.21/0.49    inference(rectify,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ! [X2,X0,X1] : ((sP4(X2,X0,X1) | ! [X3] : (~r3_waybel_9(X0,X3,X2) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & (? [X3] : (r3_waybel_9(X0,X3,X2) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3)) | ~sP4(X2,X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X2,X0,X1] : (sP4(X2,X0,X1) <=> ? [X3] : (r3_waybel_9(X0,X3,X2) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3)))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    ( ! [X6,X4,X5,X3] : (~r1_waybel_0(X5,sK13(X3,X5,X6),X4) | ~m1_subset_1(X3,u1_struct_0(X5)) | r2_hidden(X3,X4) | ~sP0(X4,X5) | ~sP4(X3,X5,X6)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f224,f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v2_struct_0(sK13(X0,X1,X2)) | ~sP4(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    ( ! [X6,X4,X5,X3] : (r2_hidden(X3,X4) | ~m1_subset_1(X3,u1_struct_0(X5)) | ~r1_waybel_0(X5,sK13(X3,X5,X6),X4) | v2_struct_0(sK13(X3,X5,X6)) | ~sP0(X4,X5) | ~sP4(X3,X5,X6)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f223,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v4_orders_2(sK13(X0,X1,X2)) | ~sP4(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    ( ! [X6,X4,X5,X3] : (r2_hidden(X3,X4) | ~m1_subset_1(X3,u1_struct_0(X5)) | ~r1_waybel_0(X5,sK13(X3,X5,X6),X4) | ~v4_orders_2(sK13(X3,X5,X6)) | v2_struct_0(sK13(X3,X5,X6)) | ~sP0(X4,X5) | ~sP4(X3,X5,X6)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f222,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v7_waybel_0(sK13(X0,X1,X2)) | ~sP4(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ( ! [X6,X4,X5,X3] : (r2_hidden(X3,X4) | ~m1_subset_1(X3,u1_struct_0(X5)) | ~r1_waybel_0(X5,sK13(X3,X5,X6),X4) | ~v7_waybel_0(sK13(X3,X5,X6)) | ~v4_orders_2(sK13(X3,X5,X6)) | v2_struct_0(sK13(X3,X5,X6)) | ~sP0(X4,X5) | ~sP4(X3,X5,X6)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f216,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (l1_waybel_0(sK13(X0,X1,X2),X1) | ~sP4(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    ( ! [X6,X4,X5,X3] : (r2_hidden(X3,X4) | ~m1_subset_1(X3,u1_struct_0(X5)) | ~r1_waybel_0(X5,sK13(X3,X5,X6),X4) | ~l1_waybel_0(sK13(X3,X5,X6),X5) | ~v7_waybel_0(sK13(X3,X5,X6)) | ~v4_orders_2(sK13(X3,X5,X6)) | v2_struct_0(sK13(X3,X5,X6)) | ~sP0(X4,X5) | ~sP4(X3,X5,X6)) )),
% 0.21/0.49    inference(resolution,[],[f65,f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r3_waybel_9(X1,sK13(X0,X1,X2),X0) | ~sP4(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X4,X0,X5,X1] : (~r3_waybel_9(X1,X4,X5) | r2_hidden(X5,X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r1_waybel_0(X1,X4,X0) | ~l1_waybel_0(X4,X1) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4) | ~sP0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP0(X0,X1) | ((~r2_hidden(sK11(X0,X1),X0) & r3_waybel_9(X1,sK10(X0,X1),sK11(X0,X1)) & m1_subset_1(sK11(X0,X1),u1_struct_0(X1))) & r1_waybel_0(X1,sK10(X0,X1),X0) & l1_waybel_0(sK10(X0,X1),X1) & v7_waybel_0(sK10(X0,X1)) & v4_orders_2(sK10(X0,X1)) & ~v2_struct_0(sK10(X0,X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r3_waybel_9(X1,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_waybel_0(X1,X4,X0) | ~l1_waybel_0(X4,X1) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) | ~sP0(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f33,f35,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r3_waybel_9(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) & r1_waybel_0(X1,X2,X0) & l1_waybel_0(X2,X1) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (? [X3] : (~r2_hidden(X3,X0) & r3_waybel_9(X1,sK10(X0,X1),X3) & m1_subset_1(X3,u1_struct_0(X1))) & r1_waybel_0(X1,sK10(X0,X1),X0) & l1_waybel_0(sK10(X0,X1),X1) & v7_waybel_0(sK10(X0,X1)) & v4_orders_2(sK10(X0,X1)) & ~v2_struct_0(sK10(X0,X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X0) & r3_waybel_9(X1,sK10(X0,X1),X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r2_hidden(sK11(X0,X1),X0) & r3_waybel_9(X1,sK10(X0,X1),sK11(X0,X1)) & m1_subset_1(sK11(X0,X1),u1_struct_0(X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r3_waybel_9(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) & r1_waybel_0(X1,X2,X0) & l1_waybel_0(X2,X1) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r3_waybel_9(X1,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_waybel_0(X1,X4,X0) | ~l1_waybel_0(X4,X1) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) | ~sP0(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r3_waybel_9(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,X2,X1) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~sP0(X1,X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    sP4(sK9,sK6,sK7) | ~spl14_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f295])).
% 0.21/0.49  fof(f295,plain,(
% 0.21/0.49    spl14_20 <=> sP4(sK9,sK6,sK7)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl14_20])])).
% 0.21/0.49  fof(f365,plain,(
% 0.21/0.49    ~spl14_3 | ~spl14_5 | ~spl14_6 | ~spl14_7 | ~spl14_8 | ~spl14_9 | spl14_10 | spl14_19),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f364])).
% 0.21/0.49  fof(f364,plain,(
% 0.21/0.49    $false | (~spl14_3 | ~spl14_5 | ~spl14_6 | ~spl14_7 | ~spl14_8 | ~spl14_9 | spl14_10 | spl14_19)),
% 0.21/0.49    inference(subsumption_resolution,[],[f363,f118])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    r2_hidden(sK7,sK8) | ~spl14_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f116])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl14_5 <=> r2_hidden(sK7,sK8)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).
% 0.21/0.49  fof(f363,plain,(
% 0.21/0.49    ~r2_hidden(sK7,sK8) | (~spl14_3 | ~spl14_6 | ~spl14_7 | ~spl14_8 | ~spl14_9 | spl14_10 | spl14_19)),
% 0.21/0.49    inference(resolution,[],[f362,f292])).
% 0.21/0.49  fof(f292,plain,(
% 0.21/0.49    ~sP2(sK9,sK6,sK7) | spl14_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f291])).
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    spl14_19 <=> sP2(sK9,sK6,sK7)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).
% 0.21/0.49  fof(f362,plain,(
% 0.21/0.49    ( ! [X0] : (sP2(sK9,sK6,X0) | ~r2_hidden(X0,sK8)) ) | (~spl14_3 | ~spl14_6 | ~spl14_7 | ~spl14_8 | ~spl14_9 | spl14_10)),
% 0.21/0.49    inference(resolution,[],[f332,f108])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    r1_waybel_7(sK6,sK8,sK9) | ~spl14_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f106])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl14_3 <=> r1_waybel_7(sK6,sK8,sK9)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).
% 0.21/0.50  fof(f332,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r1_waybel_7(sK6,sK8,X1) | ~r2_hidden(X2,sK8) | sP2(X1,sK6,X2)) ) | (~spl14_6 | ~spl14_7 | ~spl14_8 | ~spl14_9 | spl14_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f331,f143])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ~v1_xboole_0(sK8) | spl14_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f141])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    spl14_10 <=> v1_xboole_0(sK8)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).
% 0.21/0.50  fof(f331,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r1_waybel_7(sK6,sK8,X1) | ~r2_hidden(X2,sK8) | sP2(X1,sK6,X2) | v1_xboole_0(sK8)) ) | (~spl14_6 | ~spl14_7 | ~spl14_8 | ~spl14_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f330,f138])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | ~spl14_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl14_9 <=> v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).
% 0.21/0.50  fof(f330,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r1_waybel_7(sK6,sK8,X1) | ~r2_hidden(X2,sK8) | sP2(X1,sK6,X2) | ~v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(sK8)) ) | (~spl14_6 | ~spl14_7 | ~spl14_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f329,f133])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) | ~spl14_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f131])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl14_8 <=> v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).
% 0.21/0.50  fof(f329,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r1_waybel_7(sK6,sK8,X1) | ~r2_hidden(X2,sK8) | sP2(X1,sK6,X2) | ~v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) | ~v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(sK8)) ) | (~spl14_6 | ~spl14_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f320,f128])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) | ~spl14_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f126])).
% 0.21/0.50  % (11017)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl14_7 <=> v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).
% 0.21/0.50  fof(f320,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r1_waybel_7(sK6,sK8,X1) | ~r2_hidden(X2,sK8) | sP2(X1,sK6,X2) | ~v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) | ~v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) | ~v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(sK8)) ) | ~spl14_6),
% 0.21/0.50    inference(resolution,[],[f123,f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) | ~r1_waybel_7(X1,X3,X0) | ~r2_hidden(X2,X3) | sP2(X0,X1,X2) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) | v1_xboole_0(X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ! [X3] : (~r1_waybel_7(X1,X3,X0) | ~r2_hidden(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) | v1_xboole_0(X3))) & ((r1_waybel_7(X1,sK12(X0,X1,X2),X0) & r2_hidden(X2,sK12(X0,X1,X2)) & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) & v13_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1))) & v2_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1))) & v1_subset_1(sK12(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) & ~v1_xboole_0(sK12(X0,X1,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f40,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X4] : (r1_waybel_7(X1,X4,X0) & r2_hidden(X2,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1))) & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1))) & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) & ~v1_xboole_0(X4)) => (r1_waybel_7(X1,sK12(X0,X1,X2),X0) & r2_hidden(X2,sK12(X0,X1,X2)) & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) & v13_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1))) & v2_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1))) & v1_subset_1(sK12(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) & ~v1_xboole_0(sK12(X0,X1,X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ! [X3] : (~r1_waybel_7(X1,X3,X0) | ~r2_hidden(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X1))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) | v1_xboole_0(X3))) & (? [X4] : (r1_waybel_7(X1,X4,X0) & r2_hidden(X2,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1))) & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1))) & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) & ~v1_xboole_0(X4)) | ~sP2(X0,X1,X2)))),
% 0.21/0.50    inference(rectify,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ! [X3] : (~r1_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X3))) & (? [X3] : (r1_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X3)) | ~sP2(X2,X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> ? [X3] : (r1_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X3)))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~spl14_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f121])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    spl14_6 <=> m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).
% 0.21/0.50  fof(f301,plain,(
% 0.21/0.50    ~spl14_4 | spl14_18),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f300])).
% 0.21/0.50  fof(f300,plain,(
% 0.21/0.50    $false | (~spl14_4 | spl14_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f289,f283])).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    sP3(sK7,sK6,sK9) | ~spl14_4),
% 0.21/0.50    inference(resolution,[],[f113,f169])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK6)) | sP3(sK7,sK6,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f168,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ~v2_struct_0(sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ((((~r2_hidden(sK9,sK7) & r1_waybel_7(sK6,sK8,sK9) & m1_subset_1(sK9,u1_struct_0(sK6))) & r2_hidden(sK7,sK8) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) & v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) & v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) & v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) & ~v1_xboole_0(sK8)) | ~v4_pre_topc(sK7,sK6)) & (! [X4] : (! [X5] : (r2_hidden(X5,sK7) | ~r1_waybel_7(sK6,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK6))) | ~r2_hidden(sK7,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(X4)) | v4_pre_topc(sK7,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f25,f29,f28,f27,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X4)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_waybel_7(sK6,X2,X3) & m1_subset_1(X3,u1_struct_0(sK6))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,sK6)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_waybel_7(sK6,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK6))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(X4)) | v4_pre_topc(X1,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_waybel_7(sK6,X2,X3) & m1_subset_1(X3,u1_struct_0(sK6))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,sK6)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_waybel_7(sK6,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK6))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(X4)) | v4_pre_topc(X1,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) => ((? [X2] : (? [X3] : (~r2_hidden(X3,sK7) & r1_waybel_7(sK6,X2,X3) & m1_subset_1(X3,u1_struct_0(sK6))) & r2_hidden(sK7,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(sK7,sK6)) & (! [X4] : (! [X5] : (r2_hidden(X5,sK7) | ~r1_waybel_7(sK6,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK6))) | ~r2_hidden(sK7,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(X4)) | v4_pre_topc(sK7,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : (~r2_hidden(X3,sK7) & r1_waybel_7(sK6,X2,X3) & m1_subset_1(X3,u1_struct_0(sK6))) & r2_hidden(sK7,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) & ~v1_xboole_0(X2)) => (? [X3] : (~r2_hidden(X3,sK7) & r1_waybel_7(sK6,sK8,X3) & m1_subset_1(X3,u1_struct_0(sK6))) & r2_hidden(sK7,sK8) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) & v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) & v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) & v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) & ~v1_xboole_0(sK8))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ? [X3] : (~r2_hidden(X3,sK7) & r1_waybel_7(sK6,sK8,X3) & m1_subset_1(X3,u1_struct_0(sK6))) => (~r2_hidden(sK9,sK7) & r1_waybel_7(sK6,sK8,sK9) & m1_subset_1(sK9,u1_struct_0(sK6)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X4)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(rectify,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X2)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X2)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f6])).
% 0.21/0.50  fof(f6,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> ! [X2] : ((! [X3] : ((r2_hidden(X3,X1) | ~r1_waybel_7(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X2)) => (r2_hidden(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_waybel_7(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f4])).
% 0.21/0.50  fof(f4,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X2)) => (r2_hidden(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_waybel_7(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow19)).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK6)) | sP3(sK7,sK6,X0) | v2_struct_0(sK6)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f167,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    v2_pre_topc(sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK6)) | sP3(sK7,sK6,X0) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f165,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    l1_pre_topc(sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK6)) | sP3(sK7,sK6,X0) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) )),
% 0.21/0.50    inference(resolution,[],[f85,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | sP3(X1,X0,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (sP3(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(definition_folding,[],[f11,f18,f17])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X1,X0,X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> sP2(X2,X0,X1)) | ~sP3(X1,X0,X2))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r1_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r1_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r1_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X3))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow19)).
% 0.21/0.50  fof(f289,plain,(
% 0.21/0.50    ~sP3(sK7,sK6,sK9) | spl14_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f287])).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    spl14_18 <=> sP3(sK7,sK6,sK9)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).
% 0.21/0.50  fof(f299,plain,(
% 0.21/0.50    ~spl14_18 | ~spl14_19 | spl14_20 | ~spl14_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f285,f111,f295,f291,f287])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    sP4(sK9,sK6,sK7) | ~sP2(sK9,sK6,sK7) | ~sP3(sK7,sK6,sK9) | ~spl14_4),
% 0.21/0.50    inference(resolution,[],[f282,f152])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~sP5(X2,X1,X0) | sP4(X0,X1,X2) | ~sP2(X0,X1,X2) | ~sP3(X2,X1,X0)) )),
% 0.21/0.50    inference(resolution,[],[f86,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X1,X0)) | ~sP2(X2,X1,X0) | ~sP3(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(X2,k2_pre_topc(X1,X0)) | ~sP2(X2,X1,X0)) & (sP2(X2,X1,X0) | ~r2_hidden(X2,k2_pre_topc(X1,X0)))) | ~sP3(X0,X1,X2))),
% 0.21/0.50    inference(rectify,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X1,X0,X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ~sP2(X2,X0,X1)) & (sP2(X2,X0,X1) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~sP3(X1,X0,X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f18])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_pre_topc(X1,X0)) | sP4(X2,X1,X0) | ~sP5(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(X2,k2_pre_topc(X1,X0)) | ~sP4(X2,X1,X0)) & (sP4(X2,X1,X0) | ~r2_hidden(X2,k2_pre_topc(X1,X0)))) | ~sP5(X0,X1,X2))),
% 0.21/0.50    inference(rectify,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X1,X0,X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ~sP4(X2,X0,X1)) & (sP4(X2,X0,X1) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~sP5(X1,X0,X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X1,X0,X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> sP4(X2,X0,X1)) | ~sP5(X1,X0,X2))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    sP5(sK7,sK6,sK9) | ~spl14_4),
% 0.21/0.50    inference(resolution,[],[f113,f175])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK6)) | sP5(sK7,sK6,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f174,f49])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK6)) | sP5(sK7,sK6,X0) | v2_struct_0(sK6)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f173,f50])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK6)) | sP5(sK7,sK6,X0) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f171,f51])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK6)) | sP5(sK7,sK6,X0) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) )),
% 0.21/0.50    inference(resolution,[],[f95,f52])).
% 0.21/0.50  % (11017)Refutation not found, incomplete strategy% (11017)------------------------------
% 0.21/0.50  % (11017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11017)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (11017)Memory used [KB]: 895
% 0.21/0.50  % (11017)Time elapsed: 0.083 s
% 0.21/0.50  % (11017)------------------------------
% 0.21/0.50  % (11017)------------------------------
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | sP5(X1,X0,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (sP5(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(definition_folding,[],[f13,f21,f20])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r3_waybel_9(X0,X3,X2) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r3_waybel_9(X0,X3,X2) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r3_waybel_9(X0,X3,X2) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow19)).
% 0.21/0.50  fof(f280,plain,(
% 0.21/0.50    spl14_17 | ~spl14_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f162,f97,f276])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl14_1 <=> v4_pre_topc(sK7,sK6)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    ~v4_pre_topc(sK7,sK6) | sP0(sK7,sK6)),
% 0.21/0.50    inference(resolution,[],[f160,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~sP1(X0,X1) | ~v4_pre_topc(X1,X0) | sP0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : (((v4_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v4_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : ((v4_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    sP1(sK6,sK7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f159,f49])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    sP1(sK6,sK7) | v2_struct_0(sK6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f158,f50])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    sP1(sK6,sK7) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f157,f51])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    sP1(sK6,sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)),
% 0.21/0.50    inference(resolution,[],[f74,f52])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(definition_folding,[],[f9,f15,f14])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> ! [X2] : ((! [X3] : ((r2_hidden(X3,X1) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1)) | (~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r1_waybel_0(X0,X2,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow19)).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    spl14_1 | ~spl14_15),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f269])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    $false | (spl14_1 | ~spl14_15)),
% 0.21/0.50    inference(subsumption_resolution,[],[f268,f163])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ~sP0(sK7,sK6) | spl14_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f161,f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ~v4_pre_topc(sK7,sK6) | spl14_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f97])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    ~sP0(sK7,sK6) | v4_pre_topc(sK7,sK6)),
% 0.21/0.50    inference(resolution,[],[f160,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v4_pre_topc(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f268,plain,(
% 0.21/0.50    sP0(sK7,sK6) | ~spl14_15),
% 0.21/0.50    inference(resolution,[],[f263,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(sK11(X0,X1),X0) | sP0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    r2_hidden(sK11(sK7,sK6),sK7) | ~spl14_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f261])).
% 0.21/0.50  fof(f261,plain,(
% 0.21/0.50    spl14_15 <=> r2_hidden(sK11(sK7,sK6),sK7)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_15])])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    spl14_1 | spl14_14),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f266])).
% 0.21/0.50  fof(f266,plain,(
% 0.21/0.50    $false | (spl14_1 | spl14_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f265,f163])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    sP0(sK7,sK6) | spl14_14),
% 0.21/0.50    inference(resolution,[],[f259,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(sK11(X0,X1),u1_struct_0(X1)) | sP0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    ~m1_subset_1(sK11(sK7,sK6),u1_struct_0(sK6)) | spl14_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f257])).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    spl14_14 <=> m1_subset_1(sK11(sK7,sK6),u1_struct_0(sK6))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    ~spl14_14 | spl14_15 | spl14_1 | ~spl14_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f255,f146,f97,f261,f257])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    spl14_11 <=> ! [X5,X4] : (r2_hidden(X5,sK7) | v1_xboole_0(X4) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~r2_hidden(sK7,X4) | ~m1_subset_1(X5,u1_struct_0(sK6)) | ~r1_waybel_7(sK6,X4,X5))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    r2_hidden(sK11(sK7,sK6),sK7) | ~m1_subset_1(sK11(sK7,sK6),u1_struct_0(sK6)) | (spl14_1 | ~spl14_11)),
% 0.21/0.50    inference(resolution,[],[f254,f195])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    sP2(sK11(sK7,sK6),sK6,sK7) | spl14_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f194,f163])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    sP0(sK7,sK6) | sP2(sK11(sK7,sK6),sK6,sK7)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f193])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    sP0(sK7,sK6) | sP0(sK7,sK6) | sP2(sK11(sK7,sK6),sK6,sK7)),
% 0.21/0.50    inference(resolution,[],[f192,f179])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    ( ! [X0] : (~sP4(sK11(X0,sK6),sK6,sK7) | sP0(X0,sK6) | sP2(sK11(X0,sK6),sK6,sK7)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f177,f170])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    ( ! [X0] : (sP3(sK7,sK6,sK11(X0,sK6)) | sP0(X0,sK6)) )),
% 0.21/0.50    inference(resolution,[],[f169,f71])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    ( ! [X0] : (sP0(X0,sK6) | ~sP4(sK11(X0,sK6),sK6,sK7) | sP2(sK11(X0,sK6),sK6,sK7) | ~sP3(sK7,sK6,sK11(X0,sK6))) )),
% 0.21/0.50    inference(resolution,[],[f176,f154])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (~sP5(X5,X4,X3) | ~sP4(X3,X4,X5) | sP2(X3,X4,X5) | ~sP3(X5,X4,X3)) )),
% 0.21/0.50    inference(resolution,[],[f87,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_pre_topc(X1,X0)) | sP2(X2,X1,X0) | ~sP3(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X1,X0)) | ~sP4(X2,X1,X0) | ~sP5(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    ( ! [X0] : (sP5(sK7,sK6,sK11(X0,sK6)) | sP0(X0,sK6)) )),
% 0.21/0.50    inference(resolution,[],[f175,f71])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP4(sK11(X0,X1),X1,X0) | sP0(X0,X1)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f191])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP4(sK11(X0,X1),X1,X0) | sP0(X0,X1) | sP0(X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f186,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_waybel_0(X1,sK10(X0,X1),X0) | sP0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_waybel_0(X1,sK10(X0,X1),X2) | sP4(sK11(X0,X1),X1,X2) | sP0(X0,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f185,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_struct_0(sK10(X0,X1)) | sP0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sP4(sK11(X0,X1),X1,X2) | ~r1_waybel_0(X1,sK10(X0,X1),X2) | v2_struct_0(sK10(X0,X1)) | sP0(X0,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f184,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v4_orders_2(sK10(X0,X1)) | sP0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sP4(sK11(X0,X1),X1,X2) | ~r1_waybel_0(X1,sK10(X0,X1),X2) | ~v4_orders_2(sK10(X0,X1)) | v2_struct_0(sK10(X0,X1)) | sP0(X0,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f183,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v7_waybel_0(sK10(X0,X1)) | sP0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sP4(sK11(X0,X1),X1,X2) | ~r1_waybel_0(X1,sK10(X0,X1),X2) | ~v7_waybel_0(sK10(X0,X1)) | ~v4_orders_2(sK10(X0,X1)) | v2_struct_0(sK10(X0,X1)) | sP0(X0,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f181,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0,X1] : (l1_waybel_0(sK10(X0,X1),X1) | sP0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sP4(sK11(X0,X1),X1,X2) | ~r1_waybel_0(X1,sK10(X0,X1),X2) | ~l1_waybel_0(sK10(X0,X1),X1) | ~v7_waybel_0(sK10(X0,X1)) | ~v4_orders_2(sK10(X0,X1)) | v2_struct_0(sK10(X0,X1)) | sP0(X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f94,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r3_waybel_9(X1,sK10(X0,X1),sK11(X0,X1)) | sP0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r3_waybel_9(X1,X3,X0) | sP4(X0,X1,X2) | ~r1_waybel_0(X1,X3,X2) | ~l1_waybel_0(X3,X1) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    ( ! [X0] : (~sP2(X0,sK6,sK7) | r2_hidden(X0,sK7) | ~m1_subset_1(X0,u1_struct_0(sK6))) ) | ~spl14_11),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f253])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK6)) | r2_hidden(X0,sK7) | ~sP2(X0,sK6,sK7) | ~sP2(X0,sK6,sK7)) ) | ~spl14_11),
% 0.21/0.50    inference(resolution,[],[f252,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X2,sK12(X0,X1,X2)) | ~sP2(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(sK7,sK12(X0,sK6,X1)) | ~m1_subset_1(X0,u1_struct_0(sK6)) | r2_hidden(X0,sK7) | ~sP2(X0,sK6,X1)) ) | ~spl14_11),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f251])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(sK7,sK12(X0,sK6,X1)) | ~m1_subset_1(X0,u1_struct_0(sK6)) | r2_hidden(X0,sK7) | ~sP2(X0,sK6,X1) | ~sP2(X0,sK6,X1)) ) | ~spl14_11),
% 0.21/0.50    inference(resolution,[],[f250,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_waybel_7(X1,sK12(X0,X1,X2),X0) | ~sP2(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_waybel_7(sK6,sK12(X0,sK6,X1),X2) | ~r2_hidden(sK7,sK12(X0,sK6,X1)) | ~m1_subset_1(X2,u1_struct_0(sK6)) | r2_hidden(X2,sK7) | ~sP2(X0,sK6,X1)) ) | ~spl14_11),
% 0.21/0.50    inference(subsumption_resolution,[],[f249,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v13_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1))) | ~sP2(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v13_waybel_0(sK12(X0,sK6,X1),k3_yellow_1(k2_struct_0(sK6))) | r2_hidden(X2,sK7) | ~r2_hidden(sK7,sK12(X0,sK6,X1)) | ~m1_subset_1(X2,u1_struct_0(sK6)) | ~r1_waybel_7(sK6,sK12(X0,sK6,X1),X2) | ~sP2(X0,sK6,X1)) ) | ~spl14_11),
% 0.21/0.50    inference(subsumption_resolution,[],[f248,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_waybel_0(sK12(X0,X1,X2),k3_yellow_1(k2_struct_0(X1))) | ~sP2(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f248,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_waybel_0(sK12(X0,sK6,X1),k3_yellow_1(k2_struct_0(sK6))) | ~v13_waybel_0(sK12(X0,sK6,X1),k3_yellow_1(k2_struct_0(sK6))) | r2_hidden(X2,sK7) | ~r2_hidden(sK7,sK12(X0,sK6,X1)) | ~m1_subset_1(X2,u1_struct_0(sK6)) | ~r1_waybel_7(sK6,sK12(X0,sK6,X1),X2) | ~sP2(X0,sK6,X1)) ) | ~spl14_11),
% 0.21/0.50    inference(subsumption_resolution,[],[f247,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_subset_1(sK12(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) | ~sP2(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_subset_1(sK12(X0,sK6,X1),u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | ~v2_waybel_0(sK12(X0,sK6,X1),k3_yellow_1(k2_struct_0(sK6))) | ~v13_waybel_0(sK12(X0,sK6,X1),k3_yellow_1(k2_struct_0(sK6))) | r2_hidden(X2,sK7) | ~r2_hidden(sK7,sK12(X0,sK6,X1)) | ~m1_subset_1(X2,u1_struct_0(sK6)) | ~r1_waybel_7(sK6,sK12(X0,sK6,X1),X2) | ~sP2(X0,sK6,X1)) ) | ~spl14_11),
% 0.21/0.50    inference(subsumption_resolution,[],[f246,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(sK12(X0,X1,X2)) | ~sP2(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_xboole_0(sK12(X0,sK6,X1)) | ~v1_subset_1(sK12(X0,sK6,X1),u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | ~v2_waybel_0(sK12(X0,sK6,X1),k3_yellow_1(k2_struct_0(sK6))) | ~v13_waybel_0(sK12(X0,sK6,X1),k3_yellow_1(k2_struct_0(sK6))) | r2_hidden(X2,sK7) | ~r2_hidden(sK7,sK12(X0,sK6,X1)) | ~m1_subset_1(X2,u1_struct_0(sK6)) | ~r1_waybel_7(sK6,sK12(X0,sK6,X1),X2) | ~sP2(X0,sK6,X1)) ) | ~spl14_11),
% 0.21/0.50    inference(resolution,[],[f147,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) | ~sP2(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | v1_xboole_0(X4) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | r2_hidden(X5,sK7) | ~r2_hidden(sK7,X4) | ~m1_subset_1(X5,u1_struct_0(sK6)) | ~r1_waybel_7(sK6,X4,X5)) ) | ~spl14_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f146])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    spl14_1 | spl14_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f146,f97])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X4,X5] : (r2_hidden(X5,sK7) | ~r1_waybel_7(sK6,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK6)) | ~r2_hidden(sK7,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | v1_xboole_0(X4) | v4_pre_topc(sK7,sK6)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    ~spl14_1 | ~spl14_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f54,f141,f97])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ~v1_xboole_0(sK8) | ~v4_pre_topc(sK7,sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ~spl14_1 | spl14_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f55,f136,f97])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    v1_subset_1(sK8,u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))) | ~v4_pre_topc(sK7,sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    ~spl14_1 | spl14_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f56,f131,f97])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) | ~v4_pre_topc(sK7,sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ~spl14_1 | spl14_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f57,f126,f97])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) | ~v4_pre_topc(sK7,sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ~spl14_1 | spl14_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f58,f121,f97])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v4_pre_topc(sK7,sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    ~spl14_1 | spl14_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f59,f116,f97])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    r2_hidden(sK7,sK8) | ~v4_pre_topc(sK7,sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    ~spl14_1 | spl14_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f60,f111,f97])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    m1_subset_1(sK9,u1_struct_0(sK6)) | ~v4_pre_topc(sK7,sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ~spl14_1 | spl14_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f61,f106,f97])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    r1_waybel_7(sK6,sK8,sK9) | ~v4_pre_topc(sK7,sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ~spl14_1 | ~spl14_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f62,f101,f97])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ~r2_hidden(sK9,sK7) | ~v4_pre_topc(sK7,sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (11008)------------------------------
% 0.21/0.50  % (11008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11008)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (11008)Memory used [KB]: 5628
% 0.21/0.50  % (11008)Time elapsed: 0.068 s
% 0.21/0.50  % (11008)------------------------------
% 0.21/0.50  % (11008)------------------------------
% 0.21/0.50  % (11019)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.50  % (10999)Success in time 0.14 s
%------------------------------------------------------------------------------
