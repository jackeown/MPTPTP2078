%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1725+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:25 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 866 expanded)
%              Number of leaves         :   48 ( 490 expanded)
%              Depth                    :    7
%              Number of atoms          : 1106 (5057 expanded)
%              Number of equality atoms :   16 (  37 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1517,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f86,f87,f92,f97,f102,f107,f112,f117,f122,f127,f132,f137,f148,f180,f185,f195,f234,f239,f249,f282,f292,f298,f305,f357,f372,f391,f401,f431,f1409,f1420,f1441,f1465,f1489,f1504,f1505,f1516])).

fof(f1516,plain,
    ( spl5_52
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_17
    | spl5_39 ),
    inference(avatar_split_clause,[],[f377,f279,f143,f134,f129,f124,f119,f114,f99,f94,f354])).

fof(f354,plain,
    ( spl5_52
  <=> k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f94,plain,
    ( spl5_8
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f99,plain,
    ( spl5_9
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f114,plain,
    ( spl5_12
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f119,plain,
    ( spl5_13
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f124,plain,
    ( spl5_14
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f129,plain,
    ( spl5_15
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f134,plain,
    ( spl5_16
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f143,plain,
    ( spl5_17
  <=> sP4(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f279,plain,
    ( spl5_39
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f377,plain,
    ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3)
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_17
    | spl5_39 ),
    inference(unit_resulting_resolution,[],[f145,f136,f131,f126,f101,f121,f96,f116,f281,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1)
      | v2_struct_0(X0)
      | ~ sP4(X0) ) ),
    inference(general_splitting,[],[f47,f58_D])).

fof(f58,plain,(
    ! [X0,X3] :
      ( sP4(X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0) ) ),
    inference(cnf_transformation,[],[f58_D])).

fof(f58_D,plain,(
    ! [X0] :
      ( ! [X3] :
          ( v2_struct_0(X3)
          | ~ m1_pre_topc(X3,X0) )
    <=> ~ sP4(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,k2_tsep_1(X0,X1,X2),X3) = k2_tsep_1(X0,X1,k2_tsep_1(X0,X2,X3))
                      | ( ( r1_tsep_1(X1,k2_tsep_1(X0,X2,X3))
                          | r1_tsep_1(X2,X3) )
                        & ( r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                          | r1_tsep_1(X1,X2) ) ) )
                    & ( k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1)
                      | r1_tsep_1(X1,X2) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,k2_tsep_1(X0,X1,X2),X3) = k2_tsep_1(X0,X1,k2_tsep_1(X0,X2,X3))
                      | ( ( r1_tsep_1(X1,k2_tsep_1(X0,X2,X3))
                          | r1_tsep_1(X2,X3) )
                        & ( r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                          | r1_tsep_1(X1,X2) ) ) )
                    & ( k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1)
                      | r1_tsep_1(X1,X2) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( ( ( ~ r1_tsep_1(X1,k2_tsep_1(X0,X2,X3))
                          & ~ r1_tsep_1(X2,X3) )
                        | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                          & ~ r1_tsep_1(X1,X2) ) )
                     => k2_tsep_1(X0,k2_tsep_1(X0,X1,X2),X3) = k2_tsep_1(X0,X1,k2_tsep_1(X0,X2,X3)) )
                    & ( ~ r1_tsep_1(X1,X2)
                     => k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tsep_1)).

fof(f281,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl5_39 ),
    inference(avatar_component_clause,[],[f279])).

fof(f116,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f114])).

fof(f96,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f121,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f101,plain,
    ( ~ v2_struct_0(sK3)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f126,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f124])).

fof(f131,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f129])).

fof(f136,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f134])).

fof(f145,plain,
    ( sP4(sK0)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f143])).

fof(f1505,plain,
    ( ~ spl5_37
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(avatar_split_clause,[],[f1474,f134,f129,f124,f119,f114,f109,f104,f99,f94,f89,f83,f268])).

fof(f268,plain,
    ( spl5_37
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f83,plain,
    ( spl5_6
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f89,plain,
    ( spl5_7
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f104,plain,
    ( spl5_10
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f109,plain,
    ( spl5_11
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f1474,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f136,f131,f126,f111,f121,f101,f106,f96,f116,f91,f85,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | r1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X3,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f85,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f91,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f106,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f111,plain,
    ( ~ v2_struct_0(sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f1504,plain,
    ( spl5_223
    | ~ spl5_3
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | spl5_21
    | spl5_24
    | ~ spl5_30
    | ~ spl5_33
    | ~ spl5_228 ),
    inference(avatar_split_clause,[],[f1491,f1486,f246,f231,f192,f177,f134,f129,f124,f109,f104,f69,f1438])).

fof(f1438,plain,
    ( spl5_223
  <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_223])])).

fof(f69,plain,
    ( spl5_3
  <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f177,plain,
    ( spl5_21
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f192,plain,
    ( spl5_24
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f231,plain,
    ( spl5_30
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f246,plain,
    ( spl5_33
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f1486,plain,
    ( spl5_228
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_228])])).

fof(f1491,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl5_3
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | spl5_21
    | spl5_24
    | ~ spl5_30
    | ~ spl5_33
    | ~ spl5_228 ),
    inference(unit_resulting_resolution,[],[f136,f111,f126,f131,f106,f71,f179,f194,f233,f248,f1488,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | r1_tsep_1(X1,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X2,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1488,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ spl5_228 ),
    inference(avatar_component_clause,[],[f1486])).

fof(f248,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f246])).

fof(f233,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f231])).

fof(f194,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f192])).

fof(f179,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f177])).

fof(f71,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f1489,plain,
    ( spl5_228
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(avatar_split_clause,[],[f1468,f134,f129,f124,f119,f114,f109,f104,f99,f94,f89,f83,f1486])).

fof(f1468,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f136,f131,f126,f121,f101,f111,f116,f106,f96,f91,f85,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
      | ~ m1_pre_topc(X2,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      | ~ m1_pre_topc(X2,X3) )
                    & ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      | ~ m1_pre_topc(X1,X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      | ~ m1_pre_topc(X2,X3) )
                    & ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      | ~ m1_pre_topc(X1,X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) )
                      & ( m1_pre_topc(X1,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tmap_1)).

fof(f1465,plain,
    ( spl5_218
    | ~ spl5_2
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | spl5_21
    | spl5_22
    | ~ spl5_30
    | ~ spl5_31
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f1452,f428,f236,f231,f182,f177,f134,f129,f124,f119,f114,f65,f1406])).

fof(f1406,plain,
    ( spl5_218
  <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_218])])).

fof(f65,plain,
    ( spl5_2
  <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f182,plain,
    ( spl5_22
  <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f236,plain,
    ( spl5_31
  <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f428,plain,
    ( spl5_62
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f1452,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ spl5_2
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | spl5_21
    | spl5_22
    | ~ spl5_30
    | ~ spl5_31
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f136,f121,f126,f131,f116,f67,f179,f184,f233,f238,f430,f52])).

fof(f430,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK2,sK3))
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f428])).

fof(f238,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f236])).

fof(f184,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f182])).

fof(f67,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f1441,plain,
    ( ~ spl5_223
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | spl5_21
    | ~ spl5_30
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1424,f295,f231,f177,f134,f129,f124,f109,f104,f1438])).

fof(f295,plain,
    ( spl5_42
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f1424,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | spl5_21
    | ~ spl5_30
    | ~ spl5_42 ),
    inference(unit_resulting_resolution,[],[f136,f131,f126,f111,f106,f179,f233,f297,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f297,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f295])).

fof(f1420,plain,
    ( k2_tsep_1(sK0,sK2,sK3) != k2_tsep_1(sK0,sK3,sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1409,plain,
    ( ~ spl5_218
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | spl5_21
    | ~ spl5_30
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f1392,f289,f231,f177,f134,f129,f124,f119,f114,f1406])).

fof(f289,plain,
    ( spl5_41
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f1392,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | spl5_21
    | ~ spl5_30
    | ~ spl5_41 ),
    inference(unit_resulting_resolution,[],[f136,f131,f126,f121,f116,f179,f233,f291,f56])).

fof(f291,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f289])).

fof(f431,plain,
    ( spl5_62
    | ~ spl5_56
    | ~ spl5_57 ),
    inference(avatar_split_clause,[],[f414,f398,f388,f428])).

fof(f388,plain,
    ( spl5_56
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f398,plain,
    ( spl5_57
  <=> k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f414,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK2,sK3))
    | ~ spl5_56
    | ~ spl5_57 ),
    inference(backward_demodulation,[],[f390,f400])).

fof(f400,plain,
    ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f398])).

fof(f390,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f388])).

fof(f401,plain,
    ( spl5_57
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_17
    | spl5_43 ),
    inference(avatar_split_clause,[],[f396,f302,f143,f134,f129,f124,f109,f104,f99,f94,f398])).

fof(f302,plain,
    ( spl5_43
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f396,plain,
    ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_17
    | spl5_43 ),
    inference(unit_resulting_resolution,[],[f145,f136,f131,f126,f101,f111,f96,f106,f304,f59])).

fof(f304,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | spl5_43 ),
    inference(avatar_component_clause,[],[f302])).

fof(f391,plain,
    ( spl5_56
    | ~ spl5_5
    | spl5_7
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(avatar_split_clause,[],[f380,f134,f129,f124,f119,f114,f109,f104,f99,f94,f89,f78,f388])).

fof(f78,plain,
    ( spl5_5
  <=> m1_pre_topc(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f380,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | ~ spl5_5
    | spl5_7
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f136,f131,f126,f121,f101,f111,f116,f106,f96,f91,f80,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
      | ~ m1_pre_topc(X1,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,
    ( m1_pre_topc(sK1,sK3)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f372,plain,
    ( spl5_3
    | ~ spl5_4
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f371,f354,f73,f69])).

fof(f73,plain,
    ( spl5_4
  <=> r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f371,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | ~ spl5_4
    | ~ spl5_52 ),
    inference(backward_demodulation,[],[f75,f356])).

fof(f356,plain,
    ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3)
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f354])).

fof(f75,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f357,plain,
    ( spl5_52
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_17
    | spl5_37 ),
    inference(avatar_split_clause,[],[f351,f268,f143,f134,f129,f124,f119,f114,f99,f94,f354])).

fof(f351,plain,
    ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3)
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_17
    | spl5_37 ),
    inference(unit_resulting_resolution,[],[f145,f136,f131,f126,f121,f101,f116,f96,f270,f59])).

fof(f270,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | spl5_37 ),
    inference(avatar_component_clause,[],[f268])).

fof(f305,plain,
    ( ~ spl5_43
    | ~ spl5_5
    | spl5_7
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(avatar_split_clause,[],[f299,f134,f129,f124,f119,f114,f109,f104,f99,f94,f89,f78,f302])).

fof(f299,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | ~ spl5_5
    | spl5_7
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f136,f101,f126,f121,f80,f96,f111,f116,f91,f106,f131,f52])).

fof(f298,plain,
    ( spl5_42
    | spl5_7
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(avatar_split_clause,[],[f293,f134,f129,f124,f119,f114,f109,f104,f89,f295])).

fof(f293,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | spl5_7
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f136,f131,f126,f121,f111,f116,f106,f91,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                  & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tsep_1)).

fof(f292,plain,
    ( spl5_41
    | spl5_7
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(avatar_split_clause,[],[f287,f134,f129,f124,f119,f114,f109,f104,f89,f289])).

fof(f287,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | spl5_7
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f136,f131,f126,f121,f111,f116,f106,f91,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f282,plain,
    ( ~ spl5_39
    | ~ spl5_5
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(avatar_split_clause,[],[f276,f134,f129,f124,f119,f114,f99,f94,f78,f279])).

fof(f276,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ spl5_5
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f136,f101,f126,f121,f116,f80,f96,f131,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f249,plain,
    ( spl5_33
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | spl5_16 ),
    inference(avatar_split_clause,[],[f214,f134,f124,f119,f114,f99,f94,f246])).

fof(f214,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f136,f126,f121,f116,f101,f96,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f239,plain,
    ( spl5_31
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | spl5_16 ),
    inference(avatar_split_clause,[],[f216,f134,f124,f109,f104,f99,f94,f236])).

fof(f216,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f136,f126,f111,f106,f101,f96,f44])).

fof(f234,plain,
    ( spl5_30
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | spl5_16 ),
    inference(avatar_split_clause,[],[f217,f134,f124,f119,f114,f109,f104,f231])).

fof(f217,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f136,f126,f121,f116,f111,f106,f44])).

fof(f195,plain,
    ( ~ spl5_24
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | spl5_16 ),
    inference(avatar_split_clause,[],[f160,f134,f124,f119,f114,f99,f94,f192])).

fof(f160,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f136,f126,f121,f116,f101,f96,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f185,plain,
    ( ~ spl5_22
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | spl5_16 ),
    inference(avatar_split_clause,[],[f162,f134,f124,f109,f104,f99,f94,f182])).

fof(f162,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f136,f126,f111,f106,f101,f96,f43])).

fof(f180,plain,
    ( ~ spl5_21
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | spl5_16 ),
    inference(avatar_split_clause,[],[f163,f134,f124,f119,f114,f109,f104,f177])).

fof(f163,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f136,f126,f121,f116,f111,f106,f43])).

fof(f148,plain,
    ( spl5_17
    | ~ spl5_12
    | spl5_13 ),
    inference(avatar_split_clause,[],[f139,f119,f114,f143])).

fof(f139,plain,
    ( sP4(sK0)
    | ~ spl5_12
    | spl5_13 ),
    inference(unit_resulting_resolution,[],[f116,f121,f58])).

fof(f137,plain,(
    ~ spl5_16 ),
    inference(avatar_split_clause,[],[f29,f134])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
          | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) )
        & m1_pre_topc(sK2,sK3) )
      | ( ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
          | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) )
        & m1_pre_topc(sK1,sK3) ) )
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f27,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                          | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                        & m1_pre_topc(X2,X3) )
                      | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                          | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                        & m1_pre_topc(X1,X3) ) )
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,X3,X1),X2)
                        | r1_tsep_1(k2_tsep_1(sK0,X1,X3),X2) )
                      & m1_pre_topc(X2,X3) )
                    | ( ( r1_tsep_1(k2_tsep_1(sK0,X2,X3),X1)
                        | r1_tsep_1(k2_tsep_1(sK0,X3,X2),X1) )
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,X3,X1),X2)
                      | r1_tsep_1(k2_tsep_1(sK0,X1,X3),X2) )
                    & m1_pre_topc(X2,X3) )
                  | ( ( r1_tsep_1(k2_tsep_1(sK0,X2,X3),X1)
                      | r1_tsep_1(k2_tsep_1(sK0,X3,X2),X1) )
                    & m1_pre_topc(X1,X3) ) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,X3,sK1),X2)
                    | r1_tsep_1(k2_tsep_1(sK0,sK1,X3),X2) )
                  & m1_pre_topc(X2,X3) )
                | ( ( r1_tsep_1(k2_tsep_1(sK0,X2,X3),sK1)
                    | r1_tsep_1(k2_tsep_1(sK0,X3,X2),sK1) )
                  & m1_pre_topc(sK1,X3) ) )
              & ~ r1_tsep_1(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,X3,sK1),X2)
                  | r1_tsep_1(k2_tsep_1(sK0,sK1,X3),X2) )
                & m1_pre_topc(X2,X3) )
              | ( ( r1_tsep_1(k2_tsep_1(sK0,X2,X3),sK1)
                  | r1_tsep_1(k2_tsep_1(sK0,X3,X2),sK1) )
                & m1_pre_topc(sK1,X3) ) )
            & ~ r1_tsep_1(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,X3,sK1),sK2)
                | r1_tsep_1(k2_tsep_1(sK0,sK1,X3),sK2) )
              & m1_pre_topc(sK2,X3) )
            | ( ( r1_tsep_1(k2_tsep_1(sK0,sK2,X3),sK1)
                | r1_tsep_1(k2_tsep_1(sK0,X3,sK2),sK1) )
              & m1_pre_topc(sK1,X3) ) )
          & ~ r1_tsep_1(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,X3,sK1),sK2)
              | r1_tsep_1(k2_tsep_1(sK0,sK1,X3),sK2) )
            & m1_pre_topc(sK2,X3) )
          | ( ( r1_tsep_1(k2_tsep_1(sK0,sK2,X3),sK1)
              | r1_tsep_1(k2_tsep_1(sK0,X3,sK2),sK1) )
            & m1_pre_topc(sK1,X3) ) )
        & ~ r1_tsep_1(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
            | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) )
          & m1_pre_topc(sK2,sK3) )
        | ( ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
            | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) )
          & m1_pre_topc(sK1,sK3) ) )
      & ~ r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      & m1_pre_topc(X2,X3) )
                    | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      & m1_pre_topc(X2,X3) )
                    | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ~ r1_tsep_1(X1,X2)
                     => ( ( m1_pre_topc(X2,X3)
                         => ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                            & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) ) )
                        & ( m1_pre_topc(X1,X3)
                         => ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                            & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) ) )
                      & ( m1_pre_topc(X1,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tmap_1)).

fof(f132,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f30,f129])).

fof(f30,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f127,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f31,f124])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f122,plain,(
    ~ spl5_13 ),
    inference(avatar_split_clause,[],[f32,f119])).

fof(f32,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f117,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f33,f114])).

fof(f33,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f112,plain,(
    ~ spl5_11 ),
    inference(avatar_split_clause,[],[f34,f109])).

fof(f34,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f107,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f35,f104])).

fof(f35,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f102,plain,(
    ~ spl5_9 ),
    inference(avatar_split_clause,[],[f36,f99])).

fof(f36,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f37,f94])).

fof(f37,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f38,f89])).

fof(f38,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f87,plain,
    ( spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f39,f83,f78])).

fof(f39,plain,
    ( m1_pre_topc(sK2,sK3)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,
    ( spl5_1
    | spl5_2
    | spl5_6 ),
    inference(avatar_split_clause,[],[f40,f83,f65,f61])).

fof(f61,plain,
    ( spl5_1
  <=> r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f40,plain,
    ( m1_pre_topc(sK2,sK3)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,
    ( spl5_5
    | spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f41,f73,f69,f78])).

fof(f41,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,
    ( spl5_1
    | spl5_2
    | spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f42,f73,f69,f65,f61])).

fof(f42,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f28])).

%------------------------------------------------------------------------------
