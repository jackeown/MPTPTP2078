%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 468 expanded)
%              Number of leaves         :   40 ( 247 expanded)
%              Depth                    :   25
%              Number of atoms          : 1159 (5549 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   29 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f361,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f94,f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f154,f159,f177,f185,f223,f276,f304,f341,f360])).

fof(f360,plain,
    ( ~ spl9_29
    | spl9_35
    | ~ spl9_38 ),
    inference(avatar_contradiction_clause,[],[f359])).

fof(f359,plain,
    ( $false
    | ~ spl9_29
    | spl9_35
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f354,f284])).

fof(f284,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | spl9_35 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl9_35
  <=> r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f354,plain,
    ( r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ spl9_29
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f222,f338,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_tmap_1(X2,X1,X0,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r1_tmap_1(X2,X1,X0,sK8(X0,X1,X2))
          & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2)) ) )
      & ( ! [X4] :
            ( r1_tmap_1(X2,X1,X0,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X2)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X2,X1,X0,X3)
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,X1,X0,sK8(X0,X1,X2))
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_tmap_1(X2,X1,X0,X3)
            & m1_subset_1(X3,u1_struct_0(X2)) ) )
      & ( ! [X4] :
            ( r1_tmap_1(X2,X1,X0,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X2)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_tmap_1(X1,X0,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X3] :
            ( r1_tmap_1(X1,X0,X2,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ! [X3] :
          ( r1_tmap_1(X1,X0,X2,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f338,plain,
    ( sP0(sK6,sK3,sK2)
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl9_38
  <=> sP0(sK6,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f222,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2))
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl9_29
  <=> m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f341,plain,
    ( spl9_38
    | ~ spl9_2
    | ~ spl9_33 ),
    inference(avatar_split_clause,[],[f340,f250,f71,f336])).

fof(f71,plain,
    ( spl9_2
  <=> v5_pre_topc(sK6,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f250,plain,
    ( spl9_33
  <=> sP1(sK2,sK3,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f340,plain,
    ( sP0(sK6,sK3,sK2)
    | ~ spl9_2
    | ~ spl9_33 ),
    inference(subsumption_resolution,[],[f334,f73])).

fof(f73,plain,
    ( v5_pre_topc(sK6,sK2,sK3)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f334,plain,
    ( ~ v5_pre_topc(sK6,sK2,sK3)
    | sP0(sK6,sK3,sK2)
    | ~ spl9_33 ),
    inference(resolution,[],[f252,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v5_pre_topc(X2,X0,X1)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( v5_pre_topc(X2,X0,X1)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v5_pre_topc(X2,X0,X1) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X1,X0,X2] :
      ( ( ( v5_pre_topc(X2,X1,X0)
          | ~ sP0(X2,X0,X1) )
        & ( sP0(X2,X0,X1)
          | ~ v5_pre_topc(X2,X1,X0) ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X1,X0,X2] :
      ( ( v5_pre_topc(X2,X1,X0)
      <=> sP0(X2,X0,X1) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f252,plain,
    ( sP1(sK2,sK3,sK6)
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f250])).

fof(f304,plain,
    ( ~ spl9_35
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_29 ),
    inference(avatar_split_clause,[],[f303,f220,f156,f151,f146,f141,f136,f131,f126,f121,f116,f111,f106,f101,f96,f91,f86,f81,f76,f66,f282])).

fof(f66,plain,
    ( spl9_1
  <=> r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f76,plain,
    ( spl9_3
  <=> r1_tmap_1(sK4,sK2,sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f81,plain,
    ( spl9_4
  <=> m1_subset_1(sK7,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f86,plain,
    ( spl9_5
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f91,plain,
    ( spl9_6
  <=> v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f96,plain,
    ( spl9_7
  <=> v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f101,plain,
    ( spl9_8
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f106,plain,
    ( spl9_9
  <=> v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f111,plain,
    ( spl9_10
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f116,plain,
    ( spl9_11
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f121,plain,
    ( spl9_12
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f126,plain,
    ( spl9_13
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f131,plain,
    ( spl9_14
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f136,plain,
    ( spl9_15
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f141,plain,
    ( spl9_16
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f146,plain,
    ( spl9_17
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f151,plain,
    ( spl9_18
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f156,plain,
    ( spl9_19
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f303,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f302,f143])).

fof(f143,plain,
    ( ~ v2_struct_0(sK3)
    | spl9_16 ),
    inference(avatar_component_clause,[],[f141])).

fof(f302,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | v2_struct_0(sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f301,f138])).

fof(f138,plain,
    ( v2_pre_topc(sK3)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f136])).

fof(f301,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f300,f133])).

fof(f133,plain,
    ( l1_pre_topc(sK3)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f131])).

fof(f300,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f299,f128])).

fof(f128,plain,
    ( ~ v2_struct_0(sK4)
    | spl9_13 ),
    inference(avatar_component_clause,[],[f126])).

fof(f299,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f298,f123])).

fof(f123,plain,
    ( v2_pre_topc(sK4)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f298,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f297,f118])).

fof(f118,plain,
    ( l1_pre_topc(sK4)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f297,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f296,f158])).

fof(f158,plain,
    ( ~ v2_struct_0(sK2)
    | spl9_19 ),
    inference(avatar_component_clause,[],[f156])).

fof(f296,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f295,f153])).

fof(f153,plain,
    ( v2_pre_topc(sK2)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f151])).

fof(f295,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_17
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f294,f148])).

fof(f148,plain,
    ( l1_pre_topc(sK2)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f294,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f293,f113])).

fof(f113,plain,
    ( v1_funct_1(sK5)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f293,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f292,f108])).

fof(f108,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f292,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f291,f103])).

fof(f103,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f291,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f290,f98])).

fof(f98,plain,
    ( v1_funct_1(sK6)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f290,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f289,f93])).

fof(f93,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f289,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f288,f88])).

fof(f88,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f288,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f287,f83])).

fof(f83,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f287,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f286,f222])).

fof(f286,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_1
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f278,f78])).

fof(f78,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f278,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ r1_tmap_1(sK4,sK2,sK5,sK7)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_1 ),
    inference(resolution,[],[f64,f68])).

fof(f68,plain,
    ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
      | ~ r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5))
      | ~ r1_tmap_1(X1,X2,X3,X5)
      | ~ m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
      | ~ r1_tmap_1(X2,X0,X4,X6)
      | ~ r1_tmap_1(X1,X2,X3,X5)
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
                              | ~ r1_tmap_1(X2,X0,X4,X6)
                              | ~ r1_tmap_1(X1,X2,X3,X5)
                              | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
                              | ~ r1_tmap_1(X2,X0,X4,X6)
                              | ~ r1_tmap_1(X1,X2,X3,X5)
                              | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( ( r1_tmap_1(X2,X0,X4,X6)
                                  & r1_tmap_1(X1,X2,X3,X5)
                                  & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6 )
                               => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tmap_1)).

fof(f276,plain,
    ( spl9_33
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19 ),
    inference(avatar_split_clause,[],[f275,f156,f151,f146,f141,f136,f131,f96,f91,f86,f250])).

fof(f275,plain,
    ( sP1(sK2,sK3,sK6)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19 ),
    inference(subsumption_resolution,[],[f274,f143])).

fof(f274,plain,
    ( sP1(sK2,sK3,sK6)
    | v2_struct_0(sK3)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19 ),
    inference(subsumption_resolution,[],[f273,f138])).

fof(f273,plain,
    ( sP1(sK2,sK3,sK6)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19 ),
    inference(subsumption_resolution,[],[f272,f133])).

fof(f272,plain,
    ( sP1(sK2,sK3,sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19 ),
    inference(subsumption_resolution,[],[f271,f158])).

fof(f271,plain,
    ( sP1(sK2,sK3,sK6)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f270,f153])).

fof(f270,plain,
    ( sP1(sK2,sK3,sK6)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f269,f148])).

fof(f269,plain,
    ( sP1(sK2,sK3,sK6)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f268,f98])).

fof(f268,plain,
    ( sP1(sK2,sK3,sK6)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f248,f93])).

fof(f248,plain,
    ( sP1(sK2,sK3,sK6)
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_5 ),
    inference(resolution,[],[f62,f88])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | sP1(X1,X0,X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f16,f20,f19])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

fof(f223,plain,
    ( spl9_29
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | spl9_23 ),
    inference(avatar_split_clause,[],[f218,f182,f111,f106,f101,f81,f220])).

fof(f182,plain,
    ( spl9_23
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f218,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2))
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | spl9_23 ),
    inference(unit_resulting_resolution,[],[f113,f184,f83,f108,f103,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f184,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl9_23 ),
    inference(avatar_component_clause,[],[f182])).

fof(f185,plain,
    ( ~ spl9_23
    | spl9_13
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f180,f174,f126,f182])).

fof(f174,plain,
    ( spl9_22
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f180,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl9_13
    | ~ spl9_22 ),
    inference(unit_resulting_resolution,[],[f128,f176,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f176,plain,
    ( l1_struct_0(sK4)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f174])).

fof(f177,plain,
    ( spl9_22
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f160,f116,f174])).

fof(f160,plain,
    ( l1_struct_0(sK4)
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f118,f54])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f159,plain,(
    ~ spl9_19 ),
    inference(avatar_split_clause,[],[f35,f156])).

fof(f35,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7)
    & v5_pre_topc(sK6,sK2,sK3)
    & r1_tmap_1(sK4,sK2,sK5,sK7)
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    & v1_funct_1(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f9,f27,f26,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
                            & v5_pre_topc(X4,X0,X1)
                            & r1_tmap_1(X2,X0,X3,X5)
                            & m1_subset_1(X5,u1_struct_0(X2)) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(X1),X3,X4),X5)
                          & v5_pre_topc(X4,sK2,X1)
                          & r1_tmap_1(X2,sK2,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(X1),X3,X4),X5)
                        & v5_pre_topc(X4,sK2,X1)
                        & r1_tmap_1(X2,sK2,X3,X5)
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2))
                & v1_funct_1(X3) )
            & l1_pre_topc(X2)
            & v2_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r1_tmap_1(X2,sK3,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),X3,X4),X5)
                      & v5_pre_topc(X4,sK2,sK3)
                      & r1_tmap_1(X2,sK2,X3,X5)
                      & m1_subset_1(X5,u1_struct_0(X2)) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                  & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))
              & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2))
              & v1_funct_1(X3) )
          & l1_pre_topc(X2)
          & v2_pre_topc(X2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r1_tmap_1(X2,sK3,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),X3,X4),X5)
                    & v5_pre_topc(X4,sK2,sK3)
                    & r1_tmap_1(X2,sK2,X3,X5)
                    & m1_subset_1(X5,u1_struct_0(X2)) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))
            & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2))
            & v1_funct_1(X3) )
        & l1_pre_topc(X2)
        & v2_pre_topc(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),X3,X4),X5)
                  & v5_pre_topc(X4,sK2,sK3)
                  & r1_tmap_1(sK4,sK2,X3,X5)
                  & m1_subset_1(X5,u1_struct_0(sK4)) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
              & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
          & v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(sK2))
          & v1_funct_1(X3) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),X3,X4),X5)
                & v5_pre_topc(X4,sK2,sK3)
                & r1_tmap_1(sK4,sK2,X3,X5)
                & m1_subset_1(X5,u1_struct_0(sK4)) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
            & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        & v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(sK2))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,X4),X5)
              & v5_pre_topc(X4,sK2,sK3)
              & r1_tmap_1(sK4,sK2,sK5,X5)
              & m1_subset_1(X5,u1_struct_0(sK4)) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X4) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
      & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,X4),X5)
            & v5_pre_topc(X4,sK2,sK3)
            & r1_tmap_1(sK4,sK2,sK5,X5)
            & m1_subset_1(X5,u1_struct_0(sK4)) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),X5)
          & v5_pre_topc(sK6,sK2,sK3)
          & r1_tmap_1(sK4,sK2,sK5,X5)
          & m1_subset_1(X5,u1_struct_0(sK4)) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X5] :
        ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),X5)
        & v5_pre_topc(sK6,sK2,sK3)
        & r1_tmap_1(sK4,sK2,sK5,X5)
        & m1_subset_1(X5,u1_struct_0(sK4)) )
   => ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7)
      & v5_pre_topc(sK6,sK2,sK3)
      & r1_tmap_1(sK4,sK2,sK5,sK7)
      & m1_subset_1(sK7,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
                          & v5_pre_topc(X4,X0,X1)
                          & r1_tmap_1(X2,X0,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
                          & v5_pre_topc(X4,X0,X1)
                          & r1_tmap_1(X2,X0,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ( ( v5_pre_topc(X4,X0,X1)
                                & r1_tmap_1(X2,X0,X3,X5) )
                             => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ( ( v5_pre_topc(X4,X0,X1)
                              & r1_tmap_1(X2,X0,X3,X5) )
                           => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tmap_1)).

fof(f154,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f36,f151])).

fof(f36,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f149,plain,(
    spl9_17 ),
    inference(avatar_split_clause,[],[f37,f146])).

fof(f37,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f144,plain,(
    ~ spl9_16 ),
    inference(avatar_split_clause,[],[f38,f141])).

fof(f38,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f139,plain,(
    spl9_15 ),
    inference(avatar_split_clause,[],[f39,f136])).

fof(f39,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f134,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f40,f131])).

fof(f40,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f129,plain,(
    ~ spl9_13 ),
    inference(avatar_split_clause,[],[f41,f126])).

fof(f41,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f124,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f42,f121])).

fof(f42,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f119,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f43,f116])).

fof(f43,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f114,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f44,f111])).

fof(f44,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f109,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f45,f106])).

fof(f45,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f104,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f46,f101])).

fof(f46,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f99,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f47,f96])).

fof(f47,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f28])).

fof(f94,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f48,f91])).

fof(f48,plain,(
    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f89,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f49,f86])).

fof(f49,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f84,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f50,f81])).

fof(f50,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f51,f76])).

fof(f51,plain,(
    r1_tmap_1(sK4,sK2,sK5,sK7) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f52,f71])).

fof(f52,plain,(
    v5_pre_topc(sK6,sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f53,f66])).

fof(f53,plain,(
    ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:54:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (22505)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (22504)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (22506)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (22514)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (22512)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (22514)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f361,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f94,f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f154,f159,f177,f185,f223,f276,f304,f341,f360])).
% 0.22/0.49  fof(f360,plain,(
% 0.22/0.49    ~spl9_29 | spl9_35 | ~spl9_38),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f359])).
% 0.22/0.49  fof(f359,plain,(
% 0.22/0.49    $false | (~spl9_29 | spl9_35 | ~spl9_38)),
% 0.22/0.49    inference(subsumption_resolution,[],[f354,f284])).
% 0.22/0.49  fof(f284,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | spl9_35),
% 0.22/0.49    inference(avatar_component_clause,[],[f282])).
% 0.22/0.49  fof(f282,plain,(
% 0.22/0.49    spl9_35 <=> r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 0.22/0.49  fof(f354,plain,(
% 0.22/0.49    r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | (~spl9_29 | ~spl9_38)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f222,f338,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X1] : (r1_tmap_1(X2,X1,X0,X4) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r1_tmap_1(X2,X1,X0,sK8(X0,X1,X2)) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2)))) & (! [X4] : (r1_tmap_1(X2,X1,X0,X4) | ~m1_subset_1(X4,u1_struct_0(X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f32,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X2,X1,X0] : (? [X3] : (~r1_tmap_1(X2,X1,X0,X3) & m1_subset_1(X3,u1_struct_0(X2))) => (~r1_tmap_1(X2,X1,X0,sK8(X0,X1,X2)) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (~r1_tmap_1(X2,X1,X0,X3) & m1_subset_1(X3,u1_struct_0(X2)))) & (! [X4] : (r1_tmap_1(X2,X1,X0,X4) | ~m1_subset_1(X4,u1_struct_0(X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.49    inference(rectify,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X2,X0,X1)))),
% 0.22/0.49    inference(nnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1))))),
% 0.22/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.49  fof(f338,plain,(
% 0.22/0.49    sP0(sK6,sK3,sK2) | ~spl9_38),
% 0.22/0.49    inference(avatar_component_clause,[],[f336])).
% 0.22/0.49  fof(f336,plain,(
% 0.22/0.49    spl9_38 <=> sP0(sK6,sK3,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).
% 0.22/0.49  fof(f222,plain,(
% 0.22/0.49    m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2)) | ~spl9_29),
% 0.22/0.49    inference(avatar_component_clause,[],[f220])).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    spl9_29 <=> m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 0.22/0.49  fof(f341,plain,(
% 0.22/0.49    spl9_38 | ~spl9_2 | ~spl9_33),
% 0.22/0.49    inference(avatar_split_clause,[],[f340,f250,f71,f336])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl9_2 <=> v5_pre_topc(sK6,sK2,sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.49  fof(f250,plain,(
% 0.22/0.49    spl9_33 <=> sP1(sK2,sK3,sK6)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 0.22/0.49  fof(f340,plain,(
% 0.22/0.49    sP0(sK6,sK3,sK2) | (~spl9_2 | ~spl9_33)),
% 0.22/0.49    inference(subsumption_resolution,[],[f334,f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    v5_pre_topc(sK6,sK2,sK3) | ~spl9_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f71])).
% 0.22/0.49  fof(f334,plain,(
% 0.22/0.49    ~v5_pre_topc(sK6,sK2,sK3) | sP0(sK6,sK3,sK2) | ~spl9_33),
% 0.22/0.49    inference(resolution,[],[f252,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v5_pre_topc(X2,X0,X1) | sP0(X2,X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((v5_pre_topc(X2,X0,X1) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v5_pre_topc(X2,X0,X1))) | ~sP1(X0,X1,X2))),
% 0.22/0.49    inference(rectify,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X1,X0,X2] : (((v5_pre_topc(X2,X1,X0) | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | ~v5_pre_topc(X2,X1,X0))) | ~sP1(X1,X0,X2))),
% 0.22/0.49    inference(nnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X1,X0,X2] : ((v5_pre_topc(X2,X1,X0) <=> sP0(X2,X0,X1)) | ~sP1(X1,X0,X2))),
% 0.22/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.49  fof(f252,plain,(
% 0.22/0.49    sP1(sK2,sK3,sK6) | ~spl9_33),
% 0.22/0.49    inference(avatar_component_clause,[],[f250])).
% 0.22/0.49  fof(f304,plain,(
% 0.22/0.49    ~spl9_35 | spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_29),
% 0.22/0.49    inference(avatar_split_clause,[],[f303,f220,f156,f151,f146,f141,f136,f131,f126,f121,f116,f111,f106,f101,f96,f91,f86,f81,f76,f66,f282])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    spl9_1 <=> r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    spl9_3 <=> r1_tmap_1(sK4,sK2,sK5,sK7)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    spl9_4 <=> m1_subset_1(sK7,u1_struct_0(sK4))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    spl9_5 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    spl9_6 <=> v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    spl9_7 <=> v1_funct_1(sK6)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    spl9_8 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    spl9_9 <=> v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    spl9_10 <=> v1_funct_1(sK5)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    spl9_11 <=> l1_pre_topc(sK4)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    spl9_12 <=> v2_pre_topc(sK4)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    spl9_13 <=> v2_struct_0(sK4)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    spl9_14 <=> l1_pre_topc(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    spl9_15 <=> v2_pre_topc(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    spl9_16 <=> v2_struct_0(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    spl9_17 <=> l1_pre_topc(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    spl9_18 <=> v2_pre_topc(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    spl9_19 <=> v2_struct_0(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.22/0.49  fof(f303,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f302,f143])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    ~v2_struct_0(sK3) | spl9_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f141])).
% 0.22/0.49  fof(f302,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | v2_struct_0(sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f301,f138])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    v2_pre_topc(sK3) | ~spl9_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f136])).
% 0.22/0.49  fof(f301,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f300,f133])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    l1_pre_topc(sK3) | ~spl9_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f131])).
% 0.22/0.49  fof(f300,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | spl9_13 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f299,f128])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    ~v2_struct_0(sK4) | spl9_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f126])).
% 0.22/0.49  fof(f299,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f298,f123])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    v2_pre_topc(sK4) | ~spl9_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f121])).
% 0.22/0.49  fof(f298,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f297,f118])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    l1_pre_topc(sK4) | ~spl9_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f116])).
% 0.22/0.49  fof(f297,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f296,f158])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    ~v2_struct_0(sK2) | spl9_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f156])).
% 0.22/0.49  fof(f296,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_17 | ~spl9_18 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f295,f153])).
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    v2_pre_topc(sK2) | ~spl9_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f151])).
% 0.22/0.49  fof(f295,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_17 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f294,f148])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    l1_pre_topc(sK2) | ~spl9_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f146])).
% 0.22/0.49  fof(f294,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f293,f113])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    v1_funct_1(sK5) | ~spl9_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f111])).
% 0.22/0.49  fof(f293,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f292,f108])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~spl9_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f106])).
% 0.22/0.49  fof(f292,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f291,f103])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~spl9_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f101])).
% 0.22/0.49  fof(f291,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f290,f98])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    v1_funct_1(sK6) | ~spl9_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f96])).
% 0.22/0.49  fof(f290,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f289,f93])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl9_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f91])).
% 0.22/0.49  fof(f289,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f288,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~spl9_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f86])).
% 0.22/0.49  fof(f288,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f287,f83])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    m1_subset_1(sK7,u1_struct_0(sK4)) | ~spl9_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f81])).
% 0.22/0.49  fof(f287,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl9_1 | ~spl9_3 | ~spl9_29)),
% 0.22/0.49    inference(subsumption_resolution,[],[f286,f222])).
% 0.22/0.49  fof(f286,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2)) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl9_1 | ~spl9_3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f278,f78])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    r1_tmap_1(sK4,sK2,sK5,sK7) | ~spl9_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f76])).
% 0.22/0.49  fof(f278,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | ~r1_tmap_1(sK4,sK2,sK5,sK7) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2)) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl9_1),
% 0.22/0.49    inference(resolution,[],[f64,f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7) | spl9_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f66])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | ~r1_tmap_1(X1,X2,X3,X5) | ~m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | (~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6)) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X0,X4,X6) & r1_tmap_1(X1,X2,X3,X5) & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6) => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)))))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tmap_1)).
% 0.22/0.49  fof(f276,plain,(
% 0.22/0.49    spl9_33 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19),
% 0.22/0.49    inference(avatar_split_clause,[],[f275,f156,f151,f146,f141,f136,f131,f96,f91,f86,f250])).
% 0.22/0.49  fof(f275,plain,(
% 0.22/0.49    sP1(sK2,sK3,sK6) | (~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19)),
% 0.22/0.49    inference(subsumption_resolution,[],[f274,f143])).
% 0.22/0.49  fof(f274,plain,(
% 0.22/0.49    sP1(sK2,sK3,sK6) | v2_struct_0(sK3) | (~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_14 | ~spl9_15 | ~spl9_17 | ~spl9_18 | spl9_19)),
% 0.22/0.49    inference(subsumption_resolution,[],[f273,f138])).
% 0.22/0.49  fof(f273,plain,(
% 0.22/0.49    sP1(sK2,sK3,sK6) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_14 | ~spl9_17 | ~spl9_18 | spl9_19)),
% 0.22/0.49    inference(subsumption_resolution,[],[f272,f133])).
% 0.22/0.49  fof(f272,plain,(
% 0.22/0.49    sP1(sK2,sK3,sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_17 | ~spl9_18 | spl9_19)),
% 0.22/0.49    inference(subsumption_resolution,[],[f271,f158])).
% 0.22/0.49  fof(f271,plain,(
% 0.22/0.49    sP1(sK2,sK3,sK6) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_17 | ~spl9_18)),
% 0.22/0.49    inference(subsumption_resolution,[],[f270,f153])).
% 0.22/0.49  fof(f270,plain,(
% 0.22/0.49    sP1(sK2,sK3,sK6) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f269,f148])).
% 0.22/0.49  fof(f269,plain,(
% 0.22/0.49    sP1(sK2,sK3,sK6) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_5 | ~spl9_6 | ~spl9_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f268,f98])).
% 0.22/0.49  fof(f268,plain,(
% 0.22/0.49    sP1(sK2,sK3,sK6) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_5 | ~spl9_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f248,f93])).
% 0.22/0.49  fof(f248,plain,(
% 0.22/0.49    sP1(sK2,sK3,sK6) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl9_5),
% 0.22/0.49    inference(resolution,[],[f62,f88])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | sP1(X1,X0,X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(definition_folding,[],[f16,f20,f19])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).
% 0.22/0.49  fof(f223,plain,(
% 0.22/0.49    spl9_29 | ~spl9_4 | ~spl9_8 | ~spl9_9 | ~spl9_10 | spl9_23),
% 0.22/0.49    inference(avatar_split_clause,[],[f218,f182,f111,f106,f101,f81,f220])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    spl9_23 <=> v1_xboole_0(u1_struct_0(sK4))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.22/0.49  fof(f218,plain,(
% 0.22/0.49    m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2)) | (~spl9_4 | ~spl9_8 | ~spl9_9 | ~spl9_10 | spl9_23)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f113,f184,f83,f108,f103,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    ~v1_xboole_0(u1_struct_0(sK4)) | spl9_23),
% 0.22/0.49    inference(avatar_component_clause,[],[f182])).
% 0.22/0.49  fof(f185,plain,(
% 0.22/0.49    ~spl9_23 | spl9_13 | ~spl9_22),
% 0.22/0.49    inference(avatar_split_clause,[],[f180,f174,f126,f182])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    spl9_22 <=> l1_struct_0(sK4)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.22/0.49  fof(f180,plain,(
% 0.22/0.49    ~v1_xboole_0(u1_struct_0(sK4)) | (spl9_13 | ~spl9_22)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f128,f176,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    l1_struct_0(sK4) | ~spl9_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f174])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    spl9_22 | ~spl9_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f160,f116,f174])).
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    l1_struct_0(sK4) | ~spl9_11),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f118,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    ~spl9_19),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f156])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ~v2_struct_0(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    (((((~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7) & v5_pre_topc(sK6,sK2,sK3) & r1_tmap_1(sK4,sK2,sK5,sK7) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f9,f27,f26,f25,f24,f23,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,sK2,X1) & r1_tmap_1(X2,sK2,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,sK2,X1) & r1_tmap_1(X2,sK2,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,sK3,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),X3,X4),X5) & v5_pre_topc(X4,sK2,sK3) & r1_tmap_1(X2,sK2,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,sK3,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),X3,X4),X5) & v5_pre_topc(X4,sK2,sK3) & r1_tmap_1(X2,sK2,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),X3,X4),X5) & v5_pre_topc(X4,sK2,sK3) & r1_tmap_1(sK4,sK2,X3,X5) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(X3)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),X3,X4),X5) & v5_pre_topc(X4,sK2,sK3) & r1_tmap_1(sK4,sK2,X3,X5) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,X4),X5) & v5_pre_topc(X4,sK2,sK3) & r1_tmap_1(sK4,sK2,sK5,X5) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ? [X4] : (? [X5] : (~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,X4),X5) & v5_pre_topc(X4,sK2,sK3) & r1_tmap_1(sK4,sK2,sK5,X5) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) => (? [X5] : (~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),X5) & v5_pre_topc(sK6,sK2,sK3) & r1_tmap_1(sK4,sK2,sK5,X5) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ? [X5] : (~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),X5) & v5_pre_topc(sK6,sK2,sK3) & r1_tmap_1(sK4,sK2,sK5,X5) & m1_subset_1(X5,u1_struct_0(sK4))) => (~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7) & v5_pre_topc(sK6,sK2,sK3) & r1_tmap_1(sK4,sK2,sK5,sK7) & m1_subset_1(sK7,u1_struct_0(sK4)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & (v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5))) & m1_subset_1(X5,u1_struct_0(X2))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3))) & (l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5)) => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5))))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f6])).
% 0.22/0.49  fof(f6,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5)) => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5))))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tmap_1)).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    spl9_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f151])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    v2_pre_topc(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    spl9_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f146])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    l1_pre_topc(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    ~spl9_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f38,f141])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ~v2_struct_0(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    spl9_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f39,f136])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    v2_pre_topc(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    spl9_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f40,f131])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    l1_pre_topc(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    ~spl9_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f41,f126])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ~v2_struct_0(sK4)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    spl9_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f42,f121])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    v2_pre_topc(sK4)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    spl9_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f43,f116])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    l1_pre_topc(sK4)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    spl9_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f44,f111])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    v1_funct_1(sK5)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    spl9_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f45,f106])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    spl9_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f46,f101])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    spl9_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f47,f96])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    v1_funct_1(sK6)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    spl9_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f48,f91])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl9_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f49,f86])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    spl9_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f50,f81])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    m1_subset_1(sK7,u1_struct_0(sK4))),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl9_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f51,f76])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    r1_tmap_1(sK4,sK2,sK5,sK7)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    spl9_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f52,f71])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    v5_pre_topc(sK6,sK2,sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ~spl9_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f53,f66])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (22514)------------------------------
% 0.22/0.49  % (22514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22514)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (22514)Memory used [KB]: 11001
% 0.22/0.49  % (22514)Time elapsed: 0.071 s
% 0.22/0.49  % (22514)------------------------------
% 0.22/0.49  % (22514)------------------------------
% 0.22/0.49  % (22511)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (22513)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (22510)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (22503)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (22497)Success in time 0.139 s
%------------------------------------------------------------------------------
