%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:08 EST 2020

% Result     : Theorem 3.21s
% Output     : Refutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  395 (2786 expanded)
%              Number of leaves         :  110 (1465 expanded)
%              Depth                    :    7
%              Number of atoms          : 2362 (12560 expanded)
%              Number of equality atoms :   10 (  30 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7690,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f76,f81,f86,f91,f96,f101,f106,f111,f116,f121,f126,f131,f140,f149,f170,f175,f180,f185,f206,f211,f216,f221,f226,f247,f252,f257,f262,f267,f288,f293,f314,f319,f324,f329,f370,f375,f380,f385,f390,f399,f404,f409,f414,f425,f433,f438,f445,f458,f463,f468,f473,f508,f513,f518,f523,f528,f533,f538,f543,f548,f553,f558,f563,f568,f573,f578,f583,f588,f593,f598,f603,f608,f613,f618,f623,f628,f633,f638,f643,f648,f653,f658,f663,f668,f673,f678,f683,f688,f693,f698,f703,f708,f713,f7516,f7518,f7531,f7536,f7640,f7642,f7644,f7689])).

fof(f7689,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_12
    | spl5_15
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f7688])).

fof(f7688,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_12
    | spl5_15
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f7681,f144])).

fof(f144,plain,
    ( r1_tsep_1(sK2,sK4)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl5_16
  <=> r1_tsep_1(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f7681,plain,
    ( ~ r1_tsep_1(sK2,sK4)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_12
    | spl5_15 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f85,f100,f90,f105,f110,f120,f125,f139,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r1_tsep_1(X3,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
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
                 => ( m1_pre_topc(X1,X2)
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

fof(f139,plain,
    ( ~ r1_tsep_1(sK4,sK1)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl5_15
  <=> r1_tsep_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f125,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl5_12
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f120,plain,
    ( m1_pre_topc(sK4,sK0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl5_11
  <=> m1_pre_topc(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f110,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_9
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f105,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_8
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f90,plain,
    ( ~ v2_struct_0(sK2)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl5_5
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f100,plain,
    ( ~ v2_struct_0(sK4)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl5_7
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f85,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f80,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl5_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f75,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f70,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f7644,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | spl5_14
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f7643])).

fof(f7643,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f144,f474])).

fof(f474,plain,
    ( ~ r1_tsep_1(sK2,sK4)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | spl5_14 ),
    inference(unit_resulting_resolution,[],[f70,f100,f80,f95,f135,f115,f130,f120,f90,f110,f75,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tsep_1(X3,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r1_tsep_1(X3,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f130,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl5_13
  <=> m1_pre_topc(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f115,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_10
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f135,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_14
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f95,plain,
    ( ~ v2_struct_0(sK3)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl5_6
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f7642,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | spl5_14
    | ~ spl5_17
    | spl5_26
    | spl5_52
    | ~ spl5_58
    | ~ spl5_78
    | ~ spl5_95 ),
    inference(avatar_contradiction_clause,[],[f7641])).

fof(f7641,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | spl5_14
    | ~ spl5_17
    | spl5_26
    | spl5_52
    | ~ spl5_58
    | ~ spl5_78
    | ~ spl5_95 ),
    inference(subsumption_resolution,[],[f494,f7638])).

fof(f7638,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_6
    | ~ spl5_10
    | ~ spl5_17
    | spl5_26
    | spl5_52
    | ~ spl5_58
    | ~ spl5_78
    | ~ spl5_95 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f95,f115,f225,f462,f522,f622,f148,f707,f57])).

fof(f707,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3))
    | ~ spl5_95 ),
    inference(avatar_component_clause,[],[f705])).

fof(f705,plain,
    ( spl5_95
  <=> m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).

fof(f148,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl5_17
  <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f622,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
    | ~ spl5_78 ),
    inference(avatar_component_clause,[],[f620])).

fof(f620,plain,
    ( spl5_78
  <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f522,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f520])).

fof(f520,plain,
    ( spl5_58
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f462,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | spl5_52 ),
    inference(avatar_component_clause,[],[f460])).

fof(f460,plain,
    ( spl5_52
  <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f225,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl5_26
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f494,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | spl5_14 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f90,f100,f95,f110,f115,f120,f135,f130,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      | ~ m1_pre_topc(X2,X3) )
                    & ( ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      | ~ m1_pre_topc(X2,X3) )
                    & ( ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f7640,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_17
    | spl5_26
    | spl5_47
    | spl5_52
    | ~ spl5_58
    | ~ spl5_78
    | ~ spl5_95 ),
    inference(avatar_contradiction_clause,[],[f7639])).

fof(f7639,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_17
    | spl5_26
    | spl5_47
    | spl5_52
    | ~ spl5_58
    | ~ spl5_78
    | ~ spl5_95 ),
    inference(subsumption_resolution,[],[f7638,f487])).

fof(f487,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | spl5_47 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f95,f100,f90,f115,f110,f120,f423,f130,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f423,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | spl5_47 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl5_47
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f7536,plain,
    ( ~ spl5_98
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_15
    | spl5_16 ),
    inference(avatar_split_clause,[],[f7521,f142,f137,f118,f108,f103,f98,f88,f83,f78,f73,f68,f7533])).

fof(f7533,plain,
    ( spl5_98
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f7521,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_15
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f70,f90,f80,f143,f110,f85,f75,f100,f105,f120,f138,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tsep_1(X3,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r1_tsep_1(X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f138,plain,
    ( r1_tsep_1(sK4,sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f137])).

fof(f143,plain,
    ( ~ r1_tsep_1(sK2,sK4)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f142])).

fof(f7531,plain,
    ( spl5_97
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f7520,f137,f128,f118,f113,f103,f98,f93,f83,f78,f73,f68,f7528])).

fof(f7528,plain,
    ( spl5_97
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f7520,plain,
    ( r1_tsep_1(sK1,sK3)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f95,f85,f100,f115,f120,f105,f130,f138,f56])).

fof(f7518,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_12
    | spl5_15
    | ~ spl5_17
    | spl5_26
    | spl5_52
    | ~ spl5_58
    | ~ spl5_78
    | ~ spl5_84 ),
    inference(avatar_contradiction_clause,[],[f7517])).

fof(f7517,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_12
    | spl5_15
    | ~ spl5_17
    | spl5_26
    | spl5_52
    | ~ spl5_58
    | ~ spl5_78
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f499,f7514])).

fof(f7514,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_8
    | ~ spl5_17
    | spl5_26
    | spl5_52
    | ~ spl5_58
    | ~ spl5_78
    | ~ spl5_84 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f85,f105,f225,f462,f522,f622,f148,f652,f57])).

fof(f652,plain,
    ( m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK3))
    | ~ spl5_84 ),
    inference(avatar_component_clause,[],[f650])).

fof(f650,plain,
    ( spl5_84
  <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f499,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_12
    | spl5_15 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f100,f90,f85,f120,f105,f110,f139,f125,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7516,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_17
    | spl5_26
    | spl5_43
    | spl5_52
    | ~ spl5_58
    | ~ spl5_78
    | ~ spl5_84 ),
    inference(avatar_contradiction_clause,[],[f7515])).

fof(f7515,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_17
    | spl5_26
    | spl5_43
    | spl5_52
    | ~ spl5_58
    | ~ spl5_78
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f7514,f480])).

fof(f480,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_12
    | spl5_43 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f85,f90,f100,f105,f120,f110,f397,f125,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f397,plain,
    ( ~ r1_tsep_1(sK1,sK4)
    | spl5_43 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl5_43
  <=> r1_tsep_1(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f713,plain,
    ( spl5_96
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f362,f108,f103,f88,f83,f78,f73,f68,f710])).

fof(f710,plain,
    ( spl5_96
  <=> m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f362,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(backward_demodulation,[],[f295,f334])).

fof(f334,plain,
    ( k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2)
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f90,f110,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(f295,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK1))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f90,f110,f85,f105,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
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
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
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
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
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
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).

fof(f708,plain,
    ( spl5_95
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f359,f113,f103,f93,f83,f78,f73,f68,f705])).

fof(f359,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f296,f338])).

fof(f338,plain,
    ( k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK3,sK1)
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f95,f115,f62])).

fof(f296,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK1))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f95,f115,f85,f105,f49])).

fof(f703,plain,
    ( spl5_94
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f356,f113,f108,f93,f88,f78,f73,f68,f700])).

fof(f700,plain,
    ( spl5_94
  <=> m1_pre_topc(sK3,k1_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f356,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK2,sK3))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f300,f339])).

fof(f339,plain,
    ( k1_tsep_1(sK0,sK3,sK2) = k1_tsep_1(sK0,sK2,sK3)
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f95,f115,f62])).

fof(f300,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f95,f115,f90,f110,f49])).

fof(f698,plain,
    ( spl5_93
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f353,f118,f103,f98,f83,f78,f73,f68,f695])).

fof(f695,plain,
    ( spl5_93
  <=> m1_pre_topc(sK4,k1_tsep_1(sK0,sK1,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f353,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK1,sK4))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f297,f342])).

fof(f342,plain,
    ( k1_tsep_1(sK0,sK4,sK1) = k1_tsep_1(sK0,sK1,sK4)
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f100,f120,f62])).

fof(f297,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK4,sK1))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f100,f120,f85,f105,f49])).

fof(f693,plain,
    ( spl5_92
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f350,f118,f108,f98,f88,f78,f73,f68,f690])).

fof(f690,plain,
    ( spl5_92
  <=> m1_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f350,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK4))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f301,f343])).

fof(f343,plain,
    ( k1_tsep_1(sK0,sK4,sK2) = k1_tsep_1(sK0,sK2,sK4)
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f100,f120,f62])).

fof(f301,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK4,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f100,f120,f90,f110,f49])).

fof(f688,plain,
    ( spl5_91
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f347,f118,f113,f98,f93,f78,f73,f68,f685])).

fof(f685,plain,
    ( spl5_91
  <=> m1_pre_topc(sK4,k1_tsep_1(sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f347,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK3,sK4))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f305,f344])).

fof(f344,plain,
    ( k1_tsep_1(sK0,sK4,sK3) = k1_tsep_1(sK0,sK3,sK4)
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f100,f120,f62])).

fof(f305,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK4,sK3))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f100,f120,f95,f115,f49])).

fof(f683,plain,
    ( spl5_90
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_7
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f309,f118,f98,f78,f73,f68,f680])).

fof(f680,plain,
    ( spl5_90
  <=> m1_pre_topc(sK4,k1_tsep_1(sK0,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f309,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK0,sK4,sK4))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_7
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f100,f120,f100,f120,f49])).

fof(f678,plain,
    ( spl5_89
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f308,f118,f113,f98,f93,f78,f73,f68,f675])).

fof(f675,plain,
    ( spl5_89
  <=> m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).

fof(f308,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK4))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f95,f115,f100,f120,f49])).

fof(f673,plain,
    ( spl5_88
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f307,f118,f108,f98,f88,f78,f73,f68,f670])).

fof(f670,plain,
    ( spl5_88
  <=> m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f307,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK4))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f90,f110,f100,f120,f49])).

fof(f668,plain,
    ( spl5_87
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f306,f118,f103,f98,f83,f78,f73,f68,f665])).

fof(f665,plain,
    ( spl5_87
  <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f306,plain,
    ( m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK4))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f85,f105,f100,f120,f49])).

fof(f663,plain,
    ( spl5_86
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f304,f113,f93,f78,f73,f68,f660])).

fof(f660,plain,
    ( spl5_86
  <=> m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f304,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK3))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_6
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f95,f115,f95,f115,f49])).

fof(f658,plain,
    ( spl5_85
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f303,f113,f108,f93,f88,f78,f73,f68,f655])).

fof(f655,plain,
    ( spl5_85
  <=> m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f303,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK3))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f90,f110,f95,f115,f49])).

fof(f653,plain,
    ( spl5_84
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f302,f113,f103,f93,f83,f78,f73,f68,f650])).

fof(f302,plain,
    ( m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK3))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f85,f105,f95,f115,f49])).

fof(f648,plain,
    ( spl5_83
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f299,f108,f88,f78,f73,f68,f645])).

fof(f645,plain,
    ( spl5_83
  <=> m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f299,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f90,f110,f90,f110,f49])).

fof(f643,plain,
    ( spl5_82
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f298,f108,f103,f88,f83,f78,f73,f68,f640])).

fof(f640,plain,
    ( spl5_82
  <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f298,plain,
    ( m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f85,f105,f90,f110,f49])).

fof(f638,plain,
    ( spl5_81
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f294,f103,f83,f78,f73,f68,f635])).

fof(f635,plain,
    ( spl5_81
  <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f294,plain,
    ( m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK1))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f85,f105,f85,f105,f49])).

fof(f633,plain,
    ( spl5_80
    | spl5_1
    | ~ spl5_3
    | spl5_7
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f283,f118,f98,f78,f68,f630])).

fof(f630,plain,
    ( spl5_80
  <=> m1_pre_topc(k2_tsep_1(sK0,sK4,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f283,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK4,sK4),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_7
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f100,f120,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
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

fof(f628,plain,
    ( spl5_79
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f282,f118,f113,f98,f93,f78,f68,f625])).

fof(f625,plain,
    ( spl5_79
  <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f282,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f100,f120,f66])).

fof(f623,plain,
    ( spl5_78
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f281,f118,f108,f98,f88,f78,f68,f620])).

fof(f281,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f100,f120,f66])).

fof(f618,plain,
    ( spl5_77
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f280,f118,f103,f98,f83,f78,f68,f615])).

fof(f615,plain,
    ( spl5_77
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f280,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK4),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f100,f120,f66])).

fof(f613,plain,
    ( spl5_76
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f279,f118,f113,f98,f93,f78,f68,f610])).

fof(f610,plain,
    ( spl5_76
  <=> m1_pre_topc(k2_tsep_1(sK0,sK4,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f279,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK4,sK3),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f95,f115,f66])).

fof(f608,plain,
    ( spl5_75
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f278,f113,f93,f78,f68,f605])).

fof(f605,plain,
    ( spl5_75
  <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f278,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK3),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f95,f115,f66])).

fof(f603,plain,
    ( spl5_74
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f277,f113,f108,f93,f88,f78,f68,f600])).

fof(f600,plain,
    ( spl5_74
  <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f277,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f95,f115,f66])).

fof(f598,plain,
    ( spl5_73
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f276,f113,f103,f93,f83,f78,f68,f595])).

fof(f595,plain,
    ( spl5_73
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f276,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f95,f115,f66])).

fof(f593,plain,
    ( spl5_72
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f275,f118,f108,f98,f88,f78,f68,f590])).

fof(f590,plain,
    ( spl5_72
  <=> m1_pre_topc(k2_tsep_1(sK0,sK4,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f275,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK4,sK2),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f90,f110,f66])).

fof(f588,plain,
    ( spl5_71
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f274,f113,f108,f93,f88,f78,f68,f585])).

fof(f585,plain,
    ( spl5_71
  <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f274,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f90,f110,f66])).

fof(f583,plain,
    ( spl5_70
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f273,f108,f88,f78,f68,f580])).

fof(f580,plain,
    ( spl5_70
  <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f273,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK2),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f90,f110,f66])).

fof(f578,plain,
    ( spl5_69
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f272,f108,f103,f88,f83,f78,f68,f575])).

fof(f575,plain,
    ( spl5_69
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f272,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f90,f110,f66])).

fof(f573,plain,
    ( spl5_68
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f271,f118,f103,f98,f83,f78,f68,f570])).

fof(f570,plain,
    ( spl5_68
  <=> m1_pre_topc(k2_tsep_1(sK0,sK4,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f271,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK4,sK1),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f85,f105,f66])).

fof(f568,plain,
    ( spl5_67
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f270,f113,f103,f93,f83,f78,f68,f565])).

fof(f565,plain,
    ( spl5_67
  <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f270,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f85,f105,f66])).

fof(f563,plain,
    ( spl5_66
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f269,f108,f103,f88,f83,f78,f68,f560])).

fof(f560,plain,
    ( spl5_66
  <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f269,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f85,f105,f66])).

fof(f558,plain,
    ( spl5_65
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f268,f103,f83,f78,f68,f555])).

fof(f555,plain,
    ( spl5_65
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f268,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK1),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f85,f105,f66])).

fof(f553,plain,
    ( spl5_64
    | spl5_1
    | ~ spl5_3
    | spl5_7
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f242,f118,f98,f78,f68,f550])).

fof(f550,plain,
    ( spl5_64
  <=> m1_pre_topc(k1_tsep_1(sK0,sK4,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f242,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK4,sK4),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_7
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f100,f120,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f548,plain,
    ( spl5_63
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f241,f118,f113,f98,f93,f78,f68,f545])).

fof(f545,plain,
    ( spl5_63
  <=> m1_pre_topc(k1_tsep_1(sK0,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f241,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK3,sK4),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f100,f120,f64])).

fof(f543,plain,
    ( spl5_62
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f240,f118,f108,f98,f88,f78,f68,f540])).

fof(f540,plain,
    ( spl5_62
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f240,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f100,f120,f64])).

fof(f538,plain,
    ( spl5_61
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f239,f118,f103,f98,f83,f78,f68,f535])).

fof(f535,plain,
    ( spl5_61
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f239,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK4),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f100,f120,f64])).

fof(f533,plain,
    ( spl5_60
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f237,f113,f93,f78,f68,f530])).

fof(f530,plain,
    ( spl5_60
  <=> m1_pre_topc(k1_tsep_1(sK0,sK3,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f237,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK3,sK3),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f95,f115,f64])).

fof(f528,plain,
    ( spl5_59
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f236,f113,f108,f93,f88,f78,f68,f525])).

fof(f525,plain,
    ( spl5_59
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f236,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f95,f115,f64])).

fof(f523,plain,
    ( spl5_58
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f235,f113,f103,f93,f83,f78,f68,f520])).

fof(f235,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f95,f115,f64])).

fof(f518,plain,
    ( spl5_57
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f232,f108,f88,f78,f68,f515])).

fof(f515,plain,
    ( spl5_57
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f232,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f90,f110,f64])).

fof(f513,plain,
    ( spl5_56
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f231,f108,f103,f88,f83,f78,f68,f510])).

fof(f510,plain,
    ( spl5_56
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f231,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f90,f110,f64])).

fof(f508,plain,
    ( spl5_55
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f227,f103,f83,f78,f68,f505])).

fof(f505,plain,
    ( spl5_55
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f227,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),sK0)
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f85,f105,f64])).

fof(f473,plain,
    ( ~ spl5_54
    | spl5_1
    | ~ spl5_3
    | spl5_7
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f201,f118,f98,f78,f68,f470])).

fof(f470,plain,
    ( spl5_54
  <=> v2_struct_0(k2_tsep_1(sK0,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f201,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK4,sK4))
    | spl5_1
    | ~ spl5_3
    | spl5_7
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f100,f120,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f468,plain,
    ( ~ spl5_53
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f200,f118,f113,f98,f93,f78,f68,f465])).

fof(f465,plain,
    ( spl5_53
  <=> v2_struct_0(k2_tsep_1(sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f200,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK4))
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f100,f120,f65])).

fof(f463,plain,
    ( ~ spl5_52
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f199,f118,f108,f98,f88,f78,f68,f460])).

fof(f199,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f100,f120,f65])).

fof(f458,plain,
    ( ~ spl5_51
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f198,f118,f103,f98,f83,f78,f68,f455])).

fof(f455,plain,
    ( spl5_51
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f198,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK4))
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f100,f120,f65])).

fof(f445,plain,
    ( ~ spl5_50
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | spl5_47 ),
    inference(avatar_split_clause,[],[f428,f422,f128,f118,f113,f108,f98,f93,f88,f78,f73,f68,f442])).

fof(f442,plain,
    ( spl5_50
  <=> r1_tsep_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f428,plain,
    ( ~ r1_tsep_1(sK4,sK2)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | spl5_47 ),
    inference(unit_resulting_resolution,[],[f70,f75,f80,f95,f90,f100,f115,f120,f110,f130,f423,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r1_tsep_1(X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f438,plain,
    ( spl5_49
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f416,f396,f128,f118,f113,f103,f98,f93,f83,f78,f73,f68,f435])).

fof(f435,plain,
    ( spl5_49
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f416,plain,
    ( r1_tsep_1(sK3,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_43 ),
    inference(unit_resulting_resolution,[],[f70,f100,f80,f95,f115,f130,f85,f120,f398,f105,f75,f55])).

fof(f398,plain,
    ( r1_tsep_1(sK1,sK4)
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f396])).

fof(f433,plain,
    ( ~ spl5_48
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11
    | spl5_15
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f415,f396,f137,f118,f103,f98,f83,f78,f73,f68,f430])).

fof(f430,plain,
    ( spl5_48
  <=> m1_pre_topc(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f415,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11
    | spl5_15
    | ~ spl5_43 ),
    inference(unit_resulting_resolution,[],[f70,f100,f80,f139,f120,f100,f85,f120,f398,f105,f75,f55])).

fof(f425,plain,
    ( spl5_47
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f417,f142,f128,f118,f113,f108,f98,f93,f88,f78,f73,f68,f422])).

fof(f417,plain,
    ( r1_tsep_1(sK3,sK2)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f70,f100,f80,f95,f115,f130,f90,f120,f144,f110,f75,f55])).

fof(f414,plain,
    ( ~ spl5_46
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f197,f118,f113,f98,f93,f78,f68,f411])).

fof(f411,plain,
    ( spl5_46
  <=> v2_struct_0(k2_tsep_1(sK0,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f197,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK4,sK3))
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f95,f115,f65])).

fof(f409,plain,
    ( ~ spl5_45
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f196,f113,f93,f78,f68,f406])).

fof(f406,plain,
    ( spl5_45
  <=> v2_struct_0(k2_tsep_1(sK0,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f196,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK3))
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f95,f115,f65])).

fof(f404,plain,
    ( ~ spl5_44
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f195,f113,f108,f93,f88,f78,f68,f401])).

fof(f401,plain,
    ( spl5_44
  <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f195,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f95,f115,f65])).

fof(f399,plain,
    ( spl5_43
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f391,f142,f123,f118,f108,f103,f98,f88,f83,f78,f73,f68,f396])).

fof(f391,plain,
    ( r1_tsep_1(sK1,sK4)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f70,f90,f80,f85,f105,f125,f100,f110,f144,f120,f75,f54])).

fof(f390,plain,
    ( ~ spl5_42
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f194,f113,f103,f93,f83,f78,f68,f387])).

fof(f387,plain,
    ( spl5_42
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f194,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f95,f115,f65])).

fof(f385,plain,
    ( ~ spl5_41
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f193,f118,f108,f98,f88,f78,f68,f382])).

fof(f382,plain,
    ( spl5_41
  <=> v2_struct_0(k2_tsep_1(sK0,sK4,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f193,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK4,sK2))
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f90,f110,f65])).

fof(f380,plain,
    ( ~ spl5_40
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f192,f113,f108,f93,f88,f78,f68,f377])).

fof(f377,plain,
    ( spl5_40
  <=> v2_struct_0(k2_tsep_1(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f192,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f90,f110,f65])).

fof(f375,plain,
    ( ~ spl5_39
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f191,f108,f88,f78,f68,f372])).

fof(f372,plain,
    ( spl5_39
  <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f191,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK2))
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f90,f110,f65])).

fof(f370,plain,
    ( ~ spl5_38
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f190,f108,f103,f88,f83,f78,f68,f367])).

fof(f367,plain,
    ( spl5_38
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f190,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f90,f110,f65])).

fof(f329,plain,
    ( ~ spl5_37
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f189,f118,f103,f98,f83,f78,f68,f326])).

fof(f326,plain,
    ( spl5_37
  <=> v2_struct_0(k2_tsep_1(sK0,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f189,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK4,sK1))
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f85,f105,f65])).

fof(f324,plain,
    ( ~ spl5_36
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f188,f113,f103,f93,f83,f78,f68,f321])).

fof(f321,plain,
    ( spl5_36
  <=> v2_struct_0(k2_tsep_1(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f188,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f85,f105,f65])).

fof(f319,plain,
    ( ~ spl5_35
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f187,f108,f103,f88,f83,f78,f68,f316])).

fof(f316,plain,
    ( spl5_35
  <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f187,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f85,f105,f65])).

fof(f314,plain,
    ( ~ spl5_34
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f186,f103,f83,f78,f68,f311])).

fof(f311,plain,
    ( spl5_34
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f186,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK1))
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f85,f105,f65])).

fof(f293,plain,
    ( ~ spl5_33
    | spl5_1
    | ~ spl5_3
    | spl5_7
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f165,f118,f98,f78,f68,f290])).

fof(f290,plain,
    ( spl5_33
  <=> v2_struct_0(k1_tsep_1(sK0,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f165,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK4,sK4))
    | spl5_1
    | ~ spl5_3
    | spl5_7
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f100,f120,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f288,plain,
    ( ~ spl5_32
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f164,f118,f113,f98,f93,f78,f68,f285])).

fof(f285,plain,
    ( spl5_32
  <=> v2_struct_0(k1_tsep_1(sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f164,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK3,sK4))
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f100,f120,f63])).

fof(f267,plain,
    ( ~ spl5_31
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f163,f118,f108,f98,f88,f78,f68,f264])).

fof(f264,plain,
    ( spl5_31
  <=> v2_struct_0(k1_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f163,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK2,sK4))
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f100,f120,f63])).

fof(f262,plain,
    ( ~ spl5_30
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f162,f118,f103,f98,f83,f78,f68,f259])).

fof(f259,plain,
    ( spl5_30
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f162,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK4))
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f100,f120,f63])).

fof(f257,plain,
    ( ~ spl5_29
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f161,f118,f113,f98,f93,f78,f68,f254])).

fof(f254,plain,
    ( spl5_29
  <=> v2_struct_0(k1_tsep_1(sK0,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f161,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK4,sK3))
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f95,f115,f63])).

fof(f252,plain,
    ( ~ spl5_28
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f160,f113,f93,f78,f68,f249])).

fof(f249,plain,
    ( spl5_28
  <=> v2_struct_0(k1_tsep_1(sK0,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f160,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK3,sK3))
    | spl5_1
    | ~ spl5_3
    | spl5_6
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f95,f115,f63])).

fof(f247,plain,
    ( ~ spl5_27
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f159,f113,f108,f93,f88,f78,f68,f244])).

fof(f244,plain,
    ( spl5_27
  <=> v2_struct_0(k1_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f159,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK2,sK3))
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f95,f115,f63])).

fof(f226,plain,
    ( ~ spl5_26
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f158,f113,f103,f93,f83,f78,f68,f223])).

fof(f158,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f95,f115,f63])).

fof(f221,plain,
    ( ~ spl5_25
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f157,f118,f108,f98,f88,f78,f68,f218])).

fof(f218,plain,
    ( spl5_25
  <=> v2_struct_0(k1_tsep_1(sK0,sK4,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f157,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK4,sK2))
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f90,f110,f63])).

fof(f216,plain,
    ( ~ spl5_24
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f156,f113,f108,f93,f88,f78,f68,f213])).

fof(f213,plain,
    ( spl5_24
  <=> v2_struct_0(k1_tsep_1(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f156,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK3,sK2))
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | spl5_6
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f90,f110,f63])).

fof(f211,plain,
    ( ~ spl5_23
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f155,f108,f88,f78,f68,f208])).

fof(f208,plain,
    ( spl5_23
  <=> v2_struct_0(k1_tsep_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f155,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK2,sK2))
    | spl5_1
    | ~ spl5_3
    | spl5_5
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f90,f110,f63])).

fof(f206,plain,
    ( ~ spl5_22
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f154,f108,f103,f88,f83,f78,f68,f203])).

fof(f203,plain,
    ( spl5_22
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f154,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f90,f110,f63])).

fof(f185,plain,
    ( ~ spl5_21
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f153,f118,f103,f98,f83,f78,f68,f182])).

fof(f182,plain,
    ( spl5_21
  <=> v2_struct_0(k1_tsep_1(sK0,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f153,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK4,sK1))
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f85,f105,f63])).

fof(f180,plain,
    ( ~ spl5_20
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f152,f113,f103,f93,f83,f78,f68,f177])).

fof(f177,plain,
    ( spl5_20
  <=> v2_struct_0(k1_tsep_1(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f152,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK3,sK1))
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f85,f105,f63])).

fof(f175,plain,
    ( ~ spl5_19
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f151,f108,f103,f88,f83,f78,f68,f172])).

fof(f172,plain,
    ( spl5_19
  <=> v2_struct_0(k1_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f151,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK2,sK1))
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f85,f105,f63])).

fof(f170,plain,
    ( ~ spl5_18
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f150,f103,f83,f78,f68,f167])).

fof(f167,plain,
    ( spl5_18
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f150,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK1))
    | spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f85,f105,f63])).

fof(f149,plain,
    ( spl5_16
    | spl5_17 ),
    inference(avatar_split_clause,[],[f47,f146,f142])).

fof(f47,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | r1_tsep_1(sK2,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ r1_tsep_1(sK4,sK1)
      | ~ r1_tsep_1(sK2,sK3) )
    & ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
      | r1_tsep_1(sK2,sK4) )
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f32,f31,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ r1_tsep_1(X4,X1)
                          | ~ r1_tsep_1(X2,X3) )
                        & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                          | r1_tsep_1(X2,X4) )
                        & m1_pre_topc(X3,X4)
                        & m1_pre_topc(X1,X2)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
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
                  ( ? [X4] :
                      ( ( ~ r1_tsep_1(X4,X1)
                        | ~ r1_tsep_1(X2,X3) )
                      & ( r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
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

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ r1_tsep_1(X4,X1)
                      | ~ r1_tsep_1(X2,X3) )
                    & ( r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,X1,X3))
                      | r1_tsep_1(X2,X4) )
                    & m1_pre_topc(X3,X4)
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X4,sK0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ r1_tsep_1(X4,sK1)
                    | ~ r1_tsep_1(X2,X3) )
                  & ( r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,sK1,X3))
                    | r1_tsep_1(X2,X4) )
                  & m1_pre_topc(X3,X4)
                  & m1_pre_topc(sK1,X2)
                  & m1_pre_topc(X4,sK0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ r1_tsep_1(X4,sK1)
                  | ~ r1_tsep_1(X2,X3) )
                & ( r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,sK1,X3))
                  | r1_tsep_1(X2,X4) )
                & m1_pre_topc(X3,X4)
                & m1_pre_topc(sK1,X2)
                & m1_pre_topc(X4,sK0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ r1_tsep_1(X4,sK1)
                | ~ r1_tsep_1(sK2,X3) )
              & ( r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,X3))
                | r1_tsep_1(sK2,X4) )
              & m1_pre_topc(X3,X4)
              & m1_pre_topc(sK1,sK2)
              & m1_pre_topc(X4,sK0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ r1_tsep_1(X4,sK1)
              | ~ r1_tsep_1(sK2,X3) )
            & ( r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,X3))
              | r1_tsep_1(sK2,X4) )
            & m1_pre_topc(X3,X4)
            & m1_pre_topc(sK1,sK2)
            & m1_pre_topc(X4,sK0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ( ~ r1_tsep_1(X4,sK1)
            | ~ r1_tsep_1(sK2,sK3) )
          & ( r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,sK3))
            | r1_tsep_1(sK2,X4) )
          & m1_pre_topc(sK3,X4)
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X4,sK0)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X4] :
        ( ( ~ r1_tsep_1(X4,sK1)
          | ~ r1_tsep_1(sK2,sK3) )
        & ( r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,sK3))
          | r1_tsep_1(sK2,X4) )
        & m1_pre_topc(sK3,X4)
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X4,sK0)
        & ~ v2_struct_0(X4) )
   => ( ( ~ r1_tsep_1(sK4,sK1)
        | ~ r1_tsep_1(sK2,sK3) )
      & ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
        | r1_tsep_1(sK2,sK4) )
      & m1_pre_topc(sK3,sK4)
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK4,sK0)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tsep_1(X4,X1)
                        | ~ r1_tsep_1(X2,X3) )
                      & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tsep_1(X4,X1)
                        | ~ r1_tsep_1(X2,X3) )
                      & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X3,X4)
                            & m1_pre_topc(X1,X2) )
                         => ( ( r1_tsep_1(X4,X1)
                              & r1_tsep_1(X2,X3) )
                            | ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                              & ~ r1_tsep_1(X2,X4) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X3,X4)
                          & m1_pre_topc(X1,X2) )
                       => ( ( r1_tsep_1(X4,X1)
                            & r1_tsep_1(X2,X3) )
                          | ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                            & ~ r1_tsep_1(X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tmap_1)).

fof(f140,plain,
    ( ~ spl5_14
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f48,f137,f133])).

fof(f48,plain,
    ( ~ r1_tsep_1(sK4,sK1)
    | ~ r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f131,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f46,f128])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f126,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f45,f123])).

fof(f45,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f121,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f44,f118])).

fof(f44,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f116,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f42,f113])).

fof(f42,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f111,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f40,f108])).

fof(f40,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f106,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f38,f103])).

fof(f38,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f101,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f43,f98])).

fof(f43,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f96,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f41,f93])).

fof(f41,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f91,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f39,f88])).

fof(f39,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f37,f83])).

fof(f37,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f36,f78])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f35,f73])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f34,f68])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (13372)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.45  % (13382)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.46  % (13374)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.47  % (13376)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.47  % (13380)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.48  % (13384)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.48  % (13395)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.49  % (13381)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.49  % (13391)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.49  % (13378)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.49  % (13377)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (13375)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.49  % (13387)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.50  % (13379)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (13373)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (13393)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.50  % (13383)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.51  % (13385)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.51  % (13389)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.51  % (13394)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.52  % (13390)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.52  % (13392)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.52  % (13386)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.52  % (13388)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 2.22/0.64  % (13388)Refutation not found, incomplete strategy% (13388)------------------------------
% 2.22/0.64  % (13388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.64  % (13388)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.64  
% 2.22/0.64  % (13388)Memory used [KB]: 2814
% 2.22/0.64  % (13388)Time elapsed: 0.239 s
% 2.22/0.64  % (13388)------------------------------
% 2.22/0.64  % (13388)------------------------------
% 2.22/0.65  % (13380)Refutation not found, incomplete strategy% (13380)------------------------------
% 2.22/0.65  % (13380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.65  % (13380)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.65  
% 2.22/0.65  % (13380)Memory used [KB]: 12281
% 2.22/0.65  % (13380)Time elapsed: 0.224 s
% 2.22/0.65  % (13380)------------------------------
% 2.22/0.65  % (13380)------------------------------
% 2.22/0.68  % (13379)Refutation not found, incomplete strategy% (13379)------------------------------
% 2.22/0.68  % (13379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.68  % (13379)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.68  
% 2.22/0.68  % (13379)Memory used [KB]: 7419
% 2.22/0.68  % (13379)Time elapsed: 0.245 s
% 2.22/0.68  % (13379)------------------------------
% 2.22/0.68  % (13379)------------------------------
% 2.64/0.73  % (13382)Refutation not found, incomplete strategy% (13382)------------------------------
% 2.64/0.73  % (13382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.73  % (13382)Termination reason: Refutation not found, incomplete strategy
% 2.64/0.73  
% 2.64/0.73  % (13382)Memory used [KB]: 11641
% 2.64/0.73  % (13382)Time elapsed: 0.306 s
% 2.64/0.73  % (13382)------------------------------
% 2.64/0.73  % (13382)------------------------------
% 3.21/0.76  % (13394)Refutation not found, incomplete strategy% (13394)------------------------------
% 3.21/0.76  % (13394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.21/0.76  % (13394)Termination reason: Refutation not found, incomplete strategy
% 3.21/0.76  
% 3.21/0.76  % (13394)Memory used [KB]: 1918
% 3.21/0.76  % (13394)Time elapsed: 0.347 s
% 3.21/0.76  % (13394)------------------------------
% 3.21/0.76  % (13394)------------------------------
% 3.21/0.80  % (13372)Refutation found. Thanks to Tanya!
% 3.21/0.80  % SZS status Theorem for theBenchmark
% 3.21/0.80  % SZS output start Proof for theBenchmark
% 3.21/0.80  fof(f7690,plain,(
% 3.21/0.80    $false),
% 3.21/0.80    inference(avatar_sat_refutation,[],[f71,f76,f81,f86,f91,f96,f101,f106,f111,f116,f121,f126,f131,f140,f149,f170,f175,f180,f185,f206,f211,f216,f221,f226,f247,f252,f257,f262,f267,f288,f293,f314,f319,f324,f329,f370,f375,f380,f385,f390,f399,f404,f409,f414,f425,f433,f438,f445,f458,f463,f468,f473,f508,f513,f518,f523,f528,f533,f538,f543,f548,f553,f558,f563,f568,f573,f578,f583,f588,f593,f598,f603,f608,f613,f618,f623,f628,f633,f638,f643,f648,f653,f658,f663,f668,f673,f678,f683,f688,f693,f698,f703,f708,f713,f7516,f7518,f7531,f7536,f7640,f7642,f7644,f7689])).
% 3.21/0.80  fof(f7689,plain,(
% 3.21/0.80    spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_5 | spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_12 | spl5_15 | ~spl5_16),
% 3.21/0.80    inference(avatar_contradiction_clause,[],[f7688])).
% 3.21/0.80  fof(f7688,plain,(
% 3.21/0.80    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_5 | spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_12 | spl5_15 | ~spl5_16)),
% 3.21/0.80    inference(subsumption_resolution,[],[f7681,f144])).
% 3.21/0.80  fof(f144,plain,(
% 3.21/0.80    r1_tsep_1(sK2,sK4) | ~spl5_16),
% 3.21/0.80    inference(avatar_component_clause,[],[f142])).
% 3.21/0.80  fof(f142,plain,(
% 3.21/0.80    spl5_16 <=> r1_tsep_1(sK2,sK4)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 3.21/0.80  fof(f7681,plain,(
% 3.21/0.80    ~r1_tsep_1(sK2,sK4) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_5 | spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_12 | spl5_15)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f85,f100,f90,f105,f110,f120,f125,f139,f56])).
% 3.21/0.80  fof(f56,plain,(
% 3.21/0.80    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | r1_tsep_1(X3,X1) | v2_struct_0(X0)) )),
% 3.21/0.80    inference(cnf_transformation,[],[f19])).
% 3.21/0.80  fof(f19,plain,(
% 3.21/0.80    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.21/0.80    inference(flattening,[],[f18])).
% 3.21/0.80  fof(f18,plain,(
% 3.21/0.80    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.21/0.80    inference(ennf_transformation,[],[f6])).
% 3.21/0.80  fof(f6,axiom,(
% 3.21/0.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 3.21/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).
% 3.21/0.80  fof(f139,plain,(
% 3.21/0.80    ~r1_tsep_1(sK4,sK1) | spl5_15),
% 3.21/0.80    inference(avatar_component_clause,[],[f137])).
% 3.21/0.80  fof(f137,plain,(
% 3.21/0.80    spl5_15 <=> r1_tsep_1(sK4,sK1)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 3.21/0.80  fof(f125,plain,(
% 3.21/0.80    m1_pre_topc(sK1,sK2) | ~spl5_12),
% 3.21/0.80    inference(avatar_component_clause,[],[f123])).
% 3.21/0.80  fof(f123,plain,(
% 3.21/0.80    spl5_12 <=> m1_pre_topc(sK1,sK2)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 3.21/0.80  fof(f120,plain,(
% 3.21/0.80    m1_pre_topc(sK4,sK0) | ~spl5_11),
% 3.21/0.80    inference(avatar_component_clause,[],[f118])).
% 3.21/0.80  fof(f118,plain,(
% 3.21/0.80    spl5_11 <=> m1_pre_topc(sK4,sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 3.21/0.80  fof(f110,plain,(
% 3.21/0.80    m1_pre_topc(sK2,sK0) | ~spl5_9),
% 3.21/0.80    inference(avatar_component_clause,[],[f108])).
% 3.21/0.80  fof(f108,plain,(
% 3.21/0.80    spl5_9 <=> m1_pre_topc(sK2,sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 3.21/0.80  fof(f105,plain,(
% 3.21/0.80    m1_pre_topc(sK1,sK0) | ~spl5_8),
% 3.21/0.80    inference(avatar_component_clause,[],[f103])).
% 3.21/0.80  fof(f103,plain,(
% 3.21/0.80    spl5_8 <=> m1_pre_topc(sK1,sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 3.21/0.80  fof(f90,plain,(
% 3.21/0.80    ~v2_struct_0(sK2) | spl5_5),
% 3.21/0.80    inference(avatar_component_clause,[],[f88])).
% 3.21/0.80  fof(f88,plain,(
% 3.21/0.80    spl5_5 <=> v2_struct_0(sK2)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 3.21/0.80  fof(f100,plain,(
% 3.21/0.80    ~v2_struct_0(sK4) | spl5_7),
% 3.21/0.80    inference(avatar_component_clause,[],[f98])).
% 3.21/0.80  fof(f98,plain,(
% 3.21/0.80    spl5_7 <=> v2_struct_0(sK4)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 3.21/0.80  fof(f85,plain,(
% 3.21/0.80    ~v2_struct_0(sK1) | spl5_4),
% 3.21/0.80    inference(avatar_component_clause,[],[f83])).
% 3.21/0.80  fof(f83,plain,(
% 3.21/0.80    spl5_4 <=> v2_struct_0(sK1)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 3.21/0.80  fof(f80,plain,(
% 3.21/0.80    l1_pre_topc(sK0) | ~spl5_3),
% 3.21/0.80    inference(avatar_component_clause,[],[f78])).
% 3.21/0.80  fof(f78,plain,(
% 3.21/0.80    spl5_3 <=> l1_pre_topc(sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 3.21/0.80  fof(f75,plain,(
% 3.21/0.80    v2_pre_topc(sK0) | ~spl5_2),
% 3.21/0.80    inference(avatar_component_clause,[],[f73])).
% 3.21/0.80  fof(f73,plain,(
% 3.21/0.80    spl5_2 <=> v2_pre_topc(sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 3.21/0.80  fof(f70,plain,(
% 3.21/0.80    ~v2_struct_0(sK0) | spl5_1),
% 3.21/0.80    inference(avatar_component_clause,[],[f68])).
% 3.21/0.80  fof(f68,plain,(
% 3.21/0.80    spl5_1 <=> v2_struct_0(sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 3.21/0.80  fof(f7644,plain,(
% 3.21/0.80    spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_6 | spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_13 | spl5_14 | ~spl5_16),
% 3.21/0.80    inference(avatar_contradiction_clause,[],[f7643])).
% 3.21/0.80  fof(f7643,plain,(
% 3.21/0.80    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_6 | spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_13 | spl5_14 | ~spl5_16)),
% 3.21/0.80    inference(subsumption_resolution,[],[f144,f474])).
% 3.21/0.80  fof(f474,plain,(
% 3.21/0.80    ~r1_tsep_1(sK2,sK4) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_6 | spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_13 | spl5_14)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f100,f80,f95,f135,f115,f130,f120,f90,f110,f75,f57])).
% 3.21/0.80  fof(f57,plain,(
% 3.21/0.80    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~r1_tsep_1(X3,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | r1_tsep_1(X3,X1) | v2_struct_0(X0)) )),
% 3.21/0.80    inference(cnf_transformation,[],[f19])).
% 3.21/0.80  fof(f130,plain,(
% 3.21/0.80    m1_pre_topc(sK3,sK4) | ~spl5_13),
% 3.21/0.80    inference(avatar_component_clause,[],[f128])).
% 3.21/0.80  fof(f128,plain,(
% 3.21/0.80    spl5_13 <=> m1_pre_topc(sK3,sK4)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 3.21/0.80  fof(f115,plain,(
% 3.21/0.80    m1_pre_topc(sK3,sK0) | ~spl5_10),
% 3.21/0.80    inference(avatar_component_clause,[],[f113])).
% 3.21/0.80  fof(f113,plain,(
% 3.21/0.80    spl5_10 <=> m1_pre_topc(sK3,sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 3.21/0.80  fof(f135,plain,(
% 3.21/0.80    ~r1_tsep_1(sK2,sK3) | spl5_14),
% 3.21/0.80    inference(avatar_component_clause,[],[f133])).
% 3.21/0.80  fof(f133,plain,(
% 3.21/0.80    spl5_14 <=> r1_tsep_1(sK2,sK3)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 3.21/0.80  fof(f95,plain,(
% 3.21/0.80    ~v2_struct_0(sK3) | spl5_6),
% 3.21/0.80    inference(avatar_component_clause,[],[f93])).
% 3.21/0.80  fof(f93,plain,(
% 3.21/0.80    spl5_6 <=> v2_struct_0(sK3)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 3.21/0.80  fof(f7642,plain,(
% 3.21/0.80    spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_6 | spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_13 | spl5_14 | ~spl5_17 | spl5_26 | spl5_52 | ~spl5_58 | ~spl5_78 | ~spl5_95),
% 3.21/0.80    inference(avatar_contradiction_clause,[],[f7641])).
% 3.21/0.80  fof(f7641,plain,(
% 3.21/0.80    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_6 | spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_13 | spl5_14 | ~spl5_17 | spl5_26 | spl5_52 | ~spl5_58 | ~spl5_78 | ~spl5_95)),
% 3.21/0.80    inference(subsumption_resolution,[],[f494,f7638])).
% 3.21/0.80  fof(f7638,plain,(
% 3.21/0.80    r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_6 | ~spl5_10 | ~spl5_17 | spl5_26 | spl5_52 | ~spl5_58 | ~spl5_78 | ~spl5_95)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f95,f115,f225,f462,f522,f622,f148,f707,f57])).
% 3.21/0.80  fof(f707,plain,(
% 3.21/0.80    m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3)) | ~spl5_95),
% 3.21/0.80    inference(avatar_component_clause,[],[f705])).
% 3.21/0.80  fof(f705,plain,(
% 3.21/0.80    spl5_95 <=> m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).
% 3.21/0.80  fof(f148,plain,(
% 3.21/0.80    r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) | ~spl5_17),
% 3.21/0.80    inference(avatar_component_clause,[],[f146])).
% 3.21/0.80  fof(f146,plain,(
% 3.21/0.80    spl5_17 <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 3.21/0.80  fof(f622,plain,(
% 3.21/0.80    m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0) | ~spl5_78),
% 3.21/0.80    inference(avatar_component_clause,[],[f620])).
% 3.21/0.80  fof(f620,plain,(
% 3.21/0.80    spl5_78 <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).
% 3.21/0.80  fof(f522,plain,(
% 3.21/0.80    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | ~spl5_58),
% 3.21/0.80    inference(avatar_component_clause,[],[f520])).
% 3.21/0.80  fof(f520,plain,(
% 3.21/0.80    spl5_58 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 3.21/0.80  fof(f462,plain,(
% 3.21/0.80    ~v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | spl5_52),
% 3.21/0.80    inference(avatar_component_clause,[],[f460])).
% 3.21/0.80  fof(f460,plain,(
% 3.21/0.80    spl5_52 <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK4))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 3.21/0.80  fof(f225,plain,(
% 3.21/0.80    ~v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | spl5_26),
% 3.21/0.80    inference(avatar_component_clause,[],[f223])).
% 3.21/0.80  fof(f223,plain,(
% 3.21/0.80    spl5_26 <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK3))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 3.21/0.80  fof(f494,plain,(
% 3.21/0.80    ~r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_6 | spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_13 | spl5_14)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f90,f100,f95,f110,f115,f120,f135,f130,f52])).
% 3.21/0.80  fof(f52,plain,(
% 3.21/0.80    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X2,X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) | v2_struct_0(X0)) )),
% 3.21/0.80    inference(cnf_transformation,[],[f17])).
% 3.21/0.80  fof(f17,plain,(
% 3.21/0.80    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) | ~m1_pre_topc(X2,X3)) & ((~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) | ~m1_pre_topc(X1,X3))) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.21/0.80    inference(flattening,[],[f16])).
% 3.21/0.80  fof(f16,plain,(
% 3.21/0.80    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((((~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) | ~m1_pre_topc(X2,X3)) & ((~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) | ~m1_pre_topc(X1,X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.21/0.80    inference(ennf_transformation,[],[f7])).
% 3.21/0.80  fof(f7,axiom,(
% 3.21/0.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => (~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2))) & (m1_pre_topc(X1,X3) => (~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)))))))))),
% 3.21/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tmap_1)).
% 3.21/0.80  fof(f7640,plain,(
% 3.21/0.80    spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_6 | spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_13 | ~spl5_17 | spl5_26 | spl5_47 | spl5_52 | ~spl5_58 | ~spl5_78 | ~spl5_95),
% 3.21/0.80    inference(avatar_contradiction_clause,[],[f7639])).
% 3.21/0.80  fof(f7639,plain,(
% 3.21/0.80    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_6 | spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_13 | ~spl5_17 | spl5_26 | spl5_47 | spl5_52 | ~spl5_58 | ~spl5_78 | ~spl5_95)),
% 3.21/0.80    inference(subsumption_resolution,[],[f7638,f487])).
% 3.21/0.80  fof(f487,plain,(
% 3.21/0.80    ~r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_6 | spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_13 | spl5_47)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f95,f100,f90,f115,f110,f120,f423,f130,f51])).
% 3.21/0.80  fof(f51,plain,(
% 3.21/0.80    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | v2_struct_0(X0)) )),
% 3.21/0.80    inference(cnf_transformation,[],[f17])).
% 3.21/0.80  fof(f423,plain,(
% 3.21/0.80    ~r1_tsep_1(sK3,sK2) | spl5_47),
% 3.21/0.80    inference(avatar_component_clause,[],[f422])).
% 3.21/0.80  fof(f422,plain,(
% 3.21/0.80    spl5_47 <=> r1_tsep_1(sK3,sK2)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 3.21/0.80  fof(f7536,plain,(
% 3.21/0.80    ~spl5_98 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_5 | spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_15 | spl5_16),
% 3.21/0.80    inference(avatar_split_clause,[],[f7521,f142,f137,f118,f108,f103,f98,f88,f83,f78,f73,f68,f7533])).
% 3.21/0.80  fof(f7533,plain,(
% 3.21/0.80    spl5_98 <=> m1_pre_topc(sK2,sK1)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).
% 3.21/0.80  fof(f7521,plain,(
% 3.21/0.80    ~m1_pre_topc(sK2,sK1) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_5 | spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_15 | spl5_16)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f90,f80,f143,f110,f85,f75,f100,f105,f120,f138,f55])).
% 3.21/0.80  fof(f55,plain,(
% 3.21/0.80    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~r1_tsep_1(X3,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | r1_tsep_1(X1,X3) | v2_struct_0(X0)) )),
% 3.21/0.80    inference(cnf_transformation,[],[f19])).
% 3.21/0.80  fof(f138,plain,(
% 3.21/0.80    r1_tsep_1(sK4,sK1) | ~spl5_15),
% 3.21/0.80    inference(avatar_component_clause,[],[f137])).
% 3.21/0.80  fof(f143,plain,(
% 3.21/0.80    ~r1_tsep_1(sK2,sK4) | spl5_16),
% 3.21/0.80    inference(avatar_component_clause,[],[f142])).
% 3.21/0.80  fof(f7531,plain,(
% 3.21/0.80    spl5_97 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_6 | spl5_7 | ~spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_13 | ~spl5_15),
% 3.21/0.80    inference(avatar_split_clause,[],[f7520,f137,f128,f118,f113,f103,f98,f93,f83,f78,f73,f68,f7528])).
% 3.21/0.80  fof(f7528,plain,(
% 3.21/0.80    spl5_97 <=> r1_tsep_1(sK1,sK3)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).
% 3.21/0.80  fof(f7520,plain,(
% 3.21/0.80    r1_tsep_1(sK1,sK3) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_6 | spl5_7 | ~spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_13 | ~spl5_15)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f95,f85,f100,f115,f120,f105,f130,f138,f56])).
% 3.21/0.80  fof(f7518,plain,(
% 3.21/0.80    spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_5 | spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_12 | spl5_15 | ~spl5_17 | spl5_26 | spl5_52 | ~spl5_58 | ~spl5_78 | ~spl5_84),
% 3.21/0.80    inference(avatar_contradiction_clause,[],[f7517])).
% 3.21/0.80  fof(f7517,plain,(
% 3.21/0.80    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_5 | spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_12 | spl5_15 | ~spl5_17 | spl5_26 | spl5_52 | ~spl5_58 | ~spl5_78 | ~spl5_84)),
% 3.21/0.80    inference(subsumption_resolution,[],[f499,f7514])).
% 3.21/0.80  fof(f7514,plain,(
% 3.21/0.80    r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_8 | ~spl5_17 | spl5_26 | spl5_52 | ~spl5_58 | ~spl5_78 | ~spl5_84)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f85,f105,f225,f462,f522,f622,f148,f652,f57])).
% 3.21/0.80  fof(f652,plain,(
% 3.21/0.80    m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK3)) | ~spl5_84),
% 3.21/0.80    inference(avatar_component_clause,[],[f650])).
% 3.21/0.80  fof(f650,plain,(
% 3.21/0.80    spl5_84 <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK3))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).
% 3.21/0.80  fof(f499,plain,(
% 3.21/0.80    ~r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_5 | spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_12 | spl5_15)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f100,f90,f85,f120,f105,f110,f139,f125,f53])).
% 3.21/0.80  fof(f53,plain,(
% 3.21/0.80    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X2,X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | v2_struct_0(X0)) )),
% 3.21/0.80    inference(cnf_transformation,[],[f17])).
% 3.21/0.80  fof(f7516,plain,(
% 3.21/0.80    spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_5 | spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_12 | ~spl5_17 | spl5_26 | spl5_43 | spl5_52 | ~spl5_58 | ~spl5_78 | ~spl5_84),
% 3.21/0.80    inference(avatar_contradiction_clause,[],[f7515])).
% 3.21/0.80  fof(f7515,plain,(
% 3.21/0.80    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_5 | spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_12 | ~spl5_17 | spl5_26 | spl5_43 | spl5_52 | ~spl5_58 | ~spl5_78 | ~spl5_84)),
% 3.21/0.80    inference(subsumption_resolution,[],[f7514,f480])).
% 3.21/0.80  fof(f480,plain,(
% 3.21/0.80    ~r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_5 | spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_12 | spl5_43)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f85,f90,f100,f105,f120,f110,f397,f125,f50])).
% 3.21/0.80  fof(f50,plain,(
% 3.21/0.80    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) | v2_struct_0(X0)) )),
% 3.21/0.80    inference(cnf_transformation,[],[f17])).
% 3.21/0.80  fof(f397,plain,(
% 3.21/0.80    ~r1_tsep_1(sK1,sK4) | spl5_43),
% 3.21/0.80    inference(avatar_component_clause,[],[f396])).
% 3.21/0.80  fof(f396,plain,(
% 3.21/0.80    spl5_43 <=> r1_tsep_1(sK1,sK4)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 3.21/0.80  fof(f713,plain,(
% 3.21/0.80    spl5_96 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9),
% 3.21/0.80    inference(avatar_split_clause,[],[f362,f108,f103,f88,f83,f78,f73,f68,f710])).
% 3.21/0.80  fof(f710,plain,(
% 3.21/0.80    spl5_96 <=> m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).
% 3.21/0.80  fof(f362,plain,(
% 3.21/0.80    m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9)),
% 3.21/0.80    inference(backward_demodulation,[],[f295,f334])).
% 3.21/0.80  fof(f334,plain,(
% 3.21/0.80    k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f90,f110,f62])).
% 3.21/0.80  fof(f62,plain,(
% 3.21/0.80    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | v2_struct_0(X0)) )),
% 3.21/0.80    inference(cnf_transformation,[],[f23])).
% 3.21/0.80  fof(f23,plain,(
% 3.21/0.80    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.21/0.80    inference(flattening,[],[f22])).
% 3.21/0.80  fof(f22,plain,(
% 3.21/0.80    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.21/0.80    inference(ennf_transformation,[],[f1])).
% 3.21/0.80  fof(f1,axiom,(
% 3.21/0.80    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1))),
% 3.21/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).
% 3.21/0.80  fof(f295,plain,(
% 3.21/0.80    m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK1)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f90,f110,f85,f105,f49])).
% 3.21/0.80  fof(f49,plain,(
% 3.21/0.80    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.21/0.80    inference(cnf_transformation,[],[f15])).
% 3.21/0.80  fof(f15,plain,(
% 3.21/0.80    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.21/0.80    inference(flattening,[],[f14])).
% 3.21/0.80  fof(f14,plain,(
% 3.21/0.80    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.21/0.80    inference(ennf_transformation,[],[f4])).
% 3.21/0.80  fof(f4,axiom,(
% 3.21/0.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 3.21/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).
% 3.21/0.80  fof(f708,plain,(
% 3.21/0.80    spl5_95 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10),
% 3.21/0.80    inference(avatar_split_clause,[],[f359,f113,f103,f93,f83,f78,f73,f68,f705])).
% 3.21/0.80  fof(f359,plain,(
% 3.21/0.80    m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10)),
% 3.21/0.80    inference(backward_demodulation,[],[f296,f338])).
% 3.21/0.80  fof(f338,plain,(
% 3.21/0.80    k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK3,sK1) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f95,f115,f62])).
% 3.21/0.80  fof(f296,plain,(
% 3.21/0.80    m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK1)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f95,f115,f85,f105,f49])).
% 3.21/0.80  fof(f703,plain,(
% 3.21/0.80    spl5_94 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10),
% 3.21/0.80    inference(avatar_split_clause,[],[f356,f113,f108,f93,f88,f78,f73,f68,f700])).
% 3.21/0.80  fof(f700,plain,(
% 3.21/0.80    spl5_94 <=> m1_pre_topc(sK3,k1_tsep_1(sK0,sK2,sK3))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).
% 3.21/0.80  fof(f356,plain,(
% 3.21/0.80    m1_pre_topc(sK3,k1_tsep_1(sK0,sK2,sK3)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10)),
% 3.21/0.80    inference(backward_demodulation,[],[f300,f339])).
% 3.21/0.80  fof(f339,plain,(
% 3.21/0.80    k1_tsep_1(sK0,sK3,sK2) = k1_tsep_1(sK0,sK2,sK3) | (spl5_1 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f95,f115,f62])).
% 3.21/0.80  fof(f300,plain,(
% 3.21/0.80    m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f95,f115,f90,f110,f49])).
% 3.21/0.80  fof(f698,plain,(
% 3.21/0.80    spl5_93 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f353,f118,f103,f98,f83,f78,f73,f68,f695])).
% 3.21/0.80  fof(f695,plain,(
% 3.21/0.80    spl5_93 <=> m1_pre_topc(sK4,k1_tsep_1(sK0,sK1,sK4))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).
% 3.21/0.80  fof(f353,plain,(
% 3.21/0.80    m1_pre_topc(sK4,k1_tsep_1(sK0,sK1,sK4)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11)),
% 3.21/0.80    inference(backward_demodulation,[],[f297,f342])).
% 3.21/0.80  fof(f342,plain,(
% 3.21/0.80    k1_tsep_1(sK0,sK4,sK1) = k1_tsep_1(sK0,sK1,sK4) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f100,f120,f62])).
% 3.21/0.80  fof(f297,plain,(
% 3.21/0.80    m1_pre_topc(sK4,k1_tsep_1(sK0,sK4,sK1)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f100,f120,f85,f105,f49])).
% 3.21/0.80  fof(f693,plain,(
% 3.21/0.80    spl5_92 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f350,f118,f108,f98,f88,f78,f73,f68,f690])).
% 3.21/0.80  fof(f690,plain,(
% 3.21/0.80    spl5_92 <=> m1_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK4))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).
% 3.21/0.80  fof(f350,plain,(
% 3.21/0.80    m1_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK4)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11)),
% 3.21/0.80    inference(backward_demodulation,[],[f301,f343])).
% 3.21/0.80  fof(f343,plain,(
% 3.21/0.80    k1_tsep_1(sK0,sK4,sK2) = k1_tsep_1(sK0,sK2,sK4) | (spl5_1 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f100,f120,f62])).
% 3.21/0.80  fof(f301,plain,(
% 3.21/0.80    m1_pre_topc(sK4,k1_tsep_1(sK0,sK4,sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f100,f120,f90,f110,f49])).
% 3.21/0.80  fof(f688,plain,(
% 3.21/0.80    spl5_91 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f347,f118,f113,f98,f93,f78,f73,f68,f685])).
% 3.21/0.80  fof(f685,plain,(
% 3.21/0.80    spl5_91 <=> m1_pre_topc(sK4,k1_tsep_1(sK0,sK3,sK4))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).
% 3.21/0.80  fof(f347,plain,(
% 3.21/0.80    m1_pre_topc(sK4,k1_tsep_1(sK0,sK3,sK4)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11)),
% 3.21/0.80    inference(backward_demodulation,[],[f305,f344])).
% 3.21/0.80  fof(f344,plain,(
% 3.21/0.80    k1_tsep_1(sK0,sK4,sK3) = k1_tsep_1(sK0,sK3,sK4) | (spl5_1 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f100,f120,f62])).
% 3.21/0.80  fof(f305,plain,(
% 3.21/0.80    m1_pre_topc(sK4,k1_tsep_1(sK0,sK4,sK3)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f100,f120,f95,f115,f49])).
% 3.21/0.80  fof(f683,plain,(
% 3.21/0.80    spl5_90 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_7 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f309,f118,f98,f78,f73,f68,f680])).
% 3.21/0.80  fof(f680,plain,(
% 3.21/0.80    spl5_90 <=> m1_pre_topc(sK4,k1_tsep_1(sK0,sK4,sK4))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).
% 3.21/0.80  fof(f309,plain,(
% 3.21/0.80    m1_pre_topc(sK4,k1_tsep_1(sK0,sK4,sK4)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_7 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f100,f120,f100,f120,f49])).
% 3.21/0.80  fof(f678,plain,(
% 3.21/0.80    spl5_89 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f308,f118,f113,f98,f93,f78,f73,f68,f675])).
% 3.21/0.80  fof(f675,plain,(
% 3.21/0.80    spl5_89 <=> m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK4))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).
% 3.21/0.80  fof(f308,plain,(
% 3.21/0.80    m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK4)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f95,f115,f100,f120,f49])).
% 3.21/0.80  fof(f673,plain,(
% 3.21/0.80    spl5_88 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f307,f118,f108,f98,f88,f78,f73,f68,f670])).
% 3.21/0.80  fof(f670,plain,(
% 3.21/0.80    spl5_88 <=> m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK4))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).
% 3.21/0.80  fof(f307,plain,(
% 3.21/0.80    m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK4)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f90,f110,f100,f120,f49])).
% 3.21/0.80  fof(f668,plain,(
% 3.21/0.80    spl5_87 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f306,f118,f103,f98,f83,f78,f73,f68,f665])).
% 3.21/0.80  fof(f665,plain,(
% 3.21/0.80    spl5_87 <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK4))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 3.21/0.80  fof(f306,plain,(
% 3.21/0.80    m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK4)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f85,f105,f100,f120,f49])).
% 3.21/0.80  fof(f663,plain,(
% 3.21/0.80    spl5_86 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_6 | ~spl5_10),
% 3.21/0.80    inference(avatar_split_clause,[],[f304,f113,f93,f78,f73,f68,f660])).
% 3.21/0.80  fof(f660,plain,(
% 3.21/0.80    spl5_86 <=> m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK3))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).
% 3.21/0.80  fof(f304,plain,(
% 3.21/0.80    m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK3)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_6 | ~spl5_10)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f95,f115,f95,f115,f49])).
% 3.21/0.80  fof(f658,plain,(
% 3.21/0.80    spl5_85 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10),
% 3.21/0.80    inference(avatar_split_clause,[],[f303,f113,f108,f93,f88,f78,f73,f68,f655])).
% 3.21/0.80  fof(f655,plain,(
% 3.21/0.80    spl5_85 <=> m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK3))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).
% 3.21/0.80  fof(f303,plain,(
% 3.21/0.80    m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK3)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f90,f110,f95,f115,f49])).
% 3.21/0.80  fof(f653,plain,(
% 3.21/0.80    spl5_84 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10),
% 3.21/0.80    inference(avatar_split_clause,[],[f302,f113,f103,f93,f83,f78,f73,f68,f650])).
% 3.21/0.80  fof(f302,plain,(
% 3.21/0.80    m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK3)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f85,f105,f95,f115,f49])).
% 3.21/0.80  fof(f648,plain,(
% 3.21/0.80    spl5_83 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_9),
% 3.21/0.80    inference(avatar_split_clause,[],[f299,f108,f88,f78,f73,f68,f645])).
% 3.21/0.80  fof(f645,plain,(
% 3.21/0.80    spl5_83 <=> m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK2))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).
% 3.21/0.80  fof(f299,plain,(
% 3.21/0.80    m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | ~spl5_9)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f90,f110,f90,f110,f49])).
% 3.21/0.80  fof(f643,plain,(
% 3.21/0.80    spl5_82 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9),
% 3.21/0.80    inference(avatar_split_clause,[],[f298,f108,f103,f88,f83,f78,f73,f68,f640])).
% 3.21/0.80  fof(f640,plain,(
% 3.21/0.80    spl5_82 <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).
% 3.21/0.80  fof(f298,plain,(
% 3.21/0.80    m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f85,f105,f90,f110,f49])).
% 3.21/0.80  fof(f638,plain,(
% 3.21/0.80    spl5_81 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_8),
% 3.21/0.80    inference(avatar_split_clause,[],[f294,f103,f83,f78,f73,f68,f635])).
% 3.21/0.80  fof(f635,plain,(
% 3.21/0.80    spl5_81 <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK1))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).
% 3.21/0.80  fof(f294,plain,(
% 3.21/0.80    m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK1)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_8)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f85,f105,f85,f105,f49])).
% 3.21/0.80  fof(f633,plain,(
% 3.21/0.80    spl5_80 | spl5_1 | ~spl5_3 | spl5_7 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f283,f118,f98,f78,f68,f630])).
% 3.21/0.80  fof(f630,plain,(
% 3.21/0.80    spl5_80 <=> m1_pre_topc(k2_tsep_1(sK0,sK4,sK4),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).
% 3.21/0.80  fof(f283,plain,(
% 3.21/0.80    m1_pre_topc(k2_tsep_1(sK0,sK4,sK4),sK0) | (spl5_1 | ~spl5_3 | spl5_7 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f100,f120,f66])).
% 3.21/0.80  fof(f66,plain,(
% 3.21/0.80    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.21/0.80    inference(cnf_transformation,[],[f27])).
% 3.21/0.80  fof(f27,plain,(
% 3.21/0.80    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.21/0.80    inference(flattening,[],[f26])).
% 3.21/0.80  fof(f26,plain,(
% 3.21/0.80    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.21/0.80    inference(ennf_transformation,[],[f11])).
% 3.21/0.80  fof(f11,plain,(
% 3.21/0.80    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 3.21/0.80    inference(pure_predicate_removal,[],[f3])).
% 3.21/0.80  fof(f3,axiom,(
% 3.21/0.80    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 3.21/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 3.21/0.80  fof(f628,plain,(
% 3.21/0.80    spl5_79 | spl5_1 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f282,f118,f113,f98,f93,f78,f68,f625])).
% 3.21/0.80  fof(f625,plain,(
% 3.21/0.80    spl5_79 <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).
% 3.21/0.80  fof(f282,plain,(
% 3.21/0.80    m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0) | (spl5_1 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f100,f120,f66])).
% 3.21/0.80  fof(f623,plain,(
% 3.21/0.80    spl5_78 | spl5_1 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f281,f118,f108,f98,f88,f78,f68,f620])).
% 3.21/0.80  fof(f281,plain,(
% 3.21/0.80    m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0) | (spl5_1 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f100,f120,f66])).
% 3.21/0.80  fof(f618,plain,(
% 3.21/0.80    spl5_77 | spl5_1 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f280,f118,f103,f98,f83,f78,f68,f615])).
% 3.21/0.80  fof(f615,plain,(
% 3.21/0.80    spl5_77 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK4),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).
% 3.21/0.80  fof(f280,plain,(
% 3.21/0.80    m1_pre_topc(k2_tsep_1(sK0,sK1,sK4),sK0) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f100,f120,f66])).
% 3.21/0.80  fof(f613,plain,(
% 3.21/0.80    spl5_76 | spl5_1 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f279,f118,f113,f98,f93,f78,f68,f610])).
% 3.21/0.80  fof(f610,plain,(
% 3.21/0.80    spl5_76 <=> m1_pre_topc(k2_tsep_1(sK0,sK4,sK3),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 3.21/0.80  fof(f279,plain,(
% 3.21/0.80    m1_pre_topc(k2_tsep_1(sK0,sK4,sK3),sK0) | (spl5_1 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f95,f115,f66])).
% 3.21/0.80  fof(f608,plain,(
% 3.21/0.80    spl5_75 | spl5_1 | ~spl5_3 | spl5_6 | ~spl5_10),
% 3.21/0.80    inference(avatar_split_clause,[],[f278,f113,f93,f78,f68,f605])).
% 3.21/0.80  fof(f605,plain,(
% 3.21/0.80    spl5_75 <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK3),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).
% 3.21/0.80  fof(f278,plain,(
% 3.21/0.80    m1_pre_topc(k2_tsep_1(sK0,sK3,sK3),sK0) | (spl5_1 | ~spl5_3 | spl5_6 | ~spl5_10)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f95,f115,f66])).
% 3.21/0.80  fof(f603,plain,(
% 3.21/0.80    spl5_74 | spl5_1 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10),
% 3.21/0.80    inference(avatar_split_clause,[],[f277,f113,f108,f93,f88,f78,f68,f600])).
% 3.21/0.80  fof(f600,plain,(
% 3.21/0.80    spl5_74 <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 3.21/0.80  fof(f277,plain,(
% 3.21/0.80    m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0) | (spl5_1 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f95,f115,f66])).
% 3.21/0.80  fof(f598,plain,(
% 3.21/0.80    spl5_73 | spl5_1 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10),
% 3.21/0.80    inference(avatar_split_clause,[],[f276,f113,f103,f93,f83,f78,f68,f595])).
% 3.21/0.80  fof(f595,plain,(
% 3.21/0.80    spl5_73 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 3.21/0.80  fof(f276,plain,(
% 3.21/0.80    m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f95,f115,f66])).
% 3.21/0.80  fof(f593,plain,(
% 3.21/0.80    spl5_72 | spl5_1 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f275,f118,f108,f98,f88,f78,f68,f590])).
% 3.21/0.80  fof(f590,plain,(
% 3.21/0.80    spl5_72 <=> m1_pre_topc(k2_tsep_1(sK0,sK4,sK2),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).
% 3.21/0.80  fof(f275,plain,(
% 3.21/0.80    m1_pre_topc(k2_tsep_1(sK0,sK4,sK2),sK0) | (spl5_1 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f90,f110,f66])).
% 3.21/0.80  fof(f588,plain,(
% 3.21/0.80    spl5_71 | spl5_1 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10),
% 3.21/0.80    inference(avatar_split_clause,[],[f274,f113,f108,f93,f88,f78,f68,f585])).
% 3.21/0.80  fof(f585,plain,(
% 3.21/0.80    spl5_71 <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).
% 3.21/0.80  fof(f274,plain,(
% 3.21/0.80    m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0) | (spl5_1 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f90,f110,f66])).
% 3.21/0.80  fof(f583,plain,(
% 3.21/0.80    spl5_70 | spl5_1 | ~spl5_3 | spl5_5 | ~spl5_9),
% 3.21/0.80    inference(avatar_split_clause,[],[f273,f108,f88,f78,f68,f580])).
% 3.21/0.80  fof(f580,plain,(
% 3.21/0.80    spl5_70 <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK2),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).
% 3.21/0.80  fof(f273,plain,(
% 3.21/0.80    m1_pre_topc(k2_tsep_1(sK0,sK2,sK2),sK0) | (spl5_1 | ~spl5_3 | spl5_5 | ~spl5_9)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f90,f110,f66])).
% 3.21/0.80  fof(f578,plain,(
% 3.21/0.80    spl5_69 | spl5_1 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9),
% 3.21/0.80    inference(avatar_split_clause,[],[f272,f108,f103,f88,f83,f78,f68,f575])).
% 3.21/0.80  fof(f575,plain,(
% 3.21/0.80    spl5_69 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).
% 3.21/0.80  fof(f272,plain,(
% 3.21/0.80    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f90,f110,f66])).
% 3.21/0.80  fof(f573,plain,(
% 3.21/0.80    spl5_68 | spl5_1 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f271,f118,f103,f98,f83,f78,f68,f570])).
% 3.21/0.80  fof(f570,plain,(
% 3.21/0.80    spl5_68 <=> m1_pre_topc(k2_tsep_1(sK0,sK4,sK1),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 3.21/0.80  fof(f271,plain,(
% 3.21/0.80    m1_pre_topc(k2_tsep_1(sK0,sK4,sK1),sK0) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f85,f105,f66])).
% 3.21/0.80  fof(f568,plain,(
% 3.21/0.80    spl5_67 | spl5_1 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10),
% 3.21/0.80    inference(avatar_split_clause,[],[f270,f113,f103,f93,f83,f78,f68,f565])).
% 3.21/0.80  fof(f565,plain,(
% 3.21/0.80    spl5_67 <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).
% 3.21/0.80  fof(f270,plain,(
% 3.21/0.80    m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f85,f105,f66])).
% 3.21/0.80  fof(f563,plain,(
% 3.21/0.80    spl5_66 | spl5_1 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9),
% 3.21/0.80    inference(avatar_split_clause,[],[f269,f108,f103,f88,f83,f78,f68,f560])).
% 3.21/0.80  fof(f560,plain,(
% 3.21/0.80    spl5_66 <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).
% 3.21/0.80  fof(f269,plain,(
% 3.21/0.80    m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f85,f105,f66])).
% 3.21/0.80  fof(f558,plain,(
% 3.21/0.80    spl5_65 | spl5_1 | ~spl5_3 | spl5_4 | ~spl5_8),
% 3.21/0.80    inference(avatar_split_clause,[],[f268,f103,f83,f78,f68,f555])).
% 3.21/0.80  fof(f555,plain,(
% 3.21/0.80    spl5_65 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK1),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 3.21/0.80  fof(f268,plain,(
% 3.21/0.80    m1_pre_topc(k2_tsep_1(sK0,sK1,sK1),sK0) | (spl5_1 | ~spl5_3 | spl5_4 | ~spl5_8)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f85,f105,f66])).
% 3.21/0.80  fof(f553,plain,(
% 3.21/0.80    spl5_64 | spl5_1 | ~spl5_3 | spl5_7 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f242,f118,f98,f78,f68,f550])).
% 3.21/0.80  fof(f550,plain,(
% 3.21/0.80    spl5_64 <=> m1_pre_topc(k1_tsep_1(sK0,sK4,sK4),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).
% 3.21/0.80  fof(f242,plain,(
% 3.21/0.80    m1_pre_topc(k1_tsep_1(sK0,sK4,sK4),sK0) | (spl5_1 | ~spl5_3 | spl5_7 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f100,f120,f64])).
% 3.21/0.80  fof(f64,plain,(
% 3.21/0.80    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.21/0.80    inference(cnf_transformation,[],[f25])).
% 3.21/0.80  fof(f25,plain,(
% 3.21/0.80    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.21/0.80    inference(flattening,[],[f24])).
% 3.21/0.80  fof(f24,plain,(
% 3.21/0.80    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.21/0.80    inference(ennf_transformation,[],[f10])).
% 3.21/0.80  fof(f10,plain,(
% 3.21/0.80    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.21/0.80    inference(pure_predicate_removal,[],[f2])).
% 3.21/0.80  fof(f2,axiom,(
% 3.21/0.80    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.21/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 3.21/0.80  fof(f548,plain,(
% 3.21/0.80    spl5_63 | spl5_1 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f241,f118,f113,f98,f93,f78,f68,f545])).
% 3.21/0.80  fof(f545,plain,(
% 3.21/0.80    spl5_63 <=> m1_pre_topc(k1_tsep_1(sK0,sK3,sK4),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 3.21/0.80  fof(f241,plain,(
% 3.21/0.80    m1_pre_topc(k1_tsep_1(sK0,sK3,sK4),sK0) | (spl5_1 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f100,f120,f64])).
% 3.21/0.80  fof(f543,plain,(
% 3.21/0.80    spl5_62 | spl5_1 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f240,f118,f108,f98,f88,f78,f68,f540])).
% 3.21/0.80  fof(f540,plain,(
% 3.21/0.80    spl5_62 <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 3.21/0.80  fof(f240,plain,(
% 3.21/0.80    m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0) | (spl5_1 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f100,f120,f64])).
% 3.21/0.80  fof(f538,plain,(
% 3.21/0.80    spl5_61 | spl5_1 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f239,f118,f103,f98,f83,f78,f68,f535])).
% 3.21/0.80  fof(f535,plain,(
% 3.21/0.80    spl5_61 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK4),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 3.21/0.80  fof(f239,plain,(
% 3.21/0.80    m1_pre_topc(k1_tsep_1(sK0,sK1,sK4),sK0) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f100,f120,f64])).
% 3.21/0.80  fof(f533,plain,(
% 3.21/0.80    spl5_60 | spl5_1 | ~spl5_3 | spl5_6 | ~spl5_10),
% 3.21/0.80    inference(avatar_split_clause,[],[f237,f113,f93,f78,f68,f530])).
% 3.21/0.80  fof(f530,plain,(
% 3.21/0.80    spl5_60 <=> m1_pre_topc(k1_tsep_1(sK0,sK3,sK3),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 3.21/0.80  fof(f237,plain,(
% 3.21/0.80    m1_pre_topc(k1_tsep_1(sK0,sK3,sK3),sK0) | (spl5_1 | ~spl5_3 | spl5_6 | ~spl5_10)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f95,f115,f64])).
% 3.21/0.80  fof(f528,plain,(
% 3.21/0.80    spl5_59 | spl5_1 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10),
% 3.21/0.80    inference(avatar_split_clause,[],[f236,f113,f108,f93,f88,f78,f68,f525])).
% 3.21/0.80  fof(f525,plain,(
% 3.21/0.80    spl5_59 <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 3.21/0.80  fof(f236,plain,(
% 3.21/0.80    m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | (spl5_1 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f95,f115,f64])).
% 3.21/0.80  fof(f523,plain,(
% 3.21/0.80    spl5_58 | spl5_1 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10),
% 3.21/0.80    inference(avatar_split_clause,[],[f235,f113,f103,f93,f83,f78,f68,f520])).
% 3.21/0.80  fof(f235,plain,(
% 3.21/0.80    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f95,f115,f64])).
% 3.21/0.80  fof(f518,plain,(
% 3.21/0.80    spl5_57 | spl5_1 | ~spl5_3 | spl5_5 | ~spl5_9),
% 3.21/0.80    inference(avatar_split_clause,[],[f232,f108,f88,f78,f68,f515])).
% 3.21/0.80  fof(f515,plain,(
% 3.21/0.80    spl5_57 <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 3.21/0.80  fof(f232,plain,(
% 3.21/0.80    m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0) | (spl5_1 | ~spl5_3 | spl5_5 | ~spl5_9)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f90,f110,f64])).
% 3.21/0.80  fof(f513,plain,(
% 3.21/0.80    spl5_56 | spl5_1 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9),
% 3.21/0.80    inference(avatar_split_clause,[],[f231,f108,f103,f88,f83,f78,f68,f510])).
% 3.21/0.80  fof(f510,plain,(
% 3.21/0.80    spl5_56 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 3.21/0.80  fof(f231,plain,(
% 3.21/0.80    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f90,f110,f64])).
% 3.21/0.80  fof(f508,plain,(
% 3.21/0.80    spl5_55 | spl5_1 | ~spl5_3 | spl5_4 | ~spl5_8),
% 3.21/0.80    inference(avatar_split_clause,[],[f227,f103,f83,f78,f68,f505])).
% 3.21/0.80  fof(f505,plain,(
% 3.21/0.80    spl5_55 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),sK0)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 3.21/0.80  fof(f227,plain,(
% 3.21/0.80    m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),sK0) | (spl5_1 | ~spl5_3 | spl5_4 | ~spl5_8)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f85,f105,f64])).
% 3.21/0.80  fof(f473,plain,(
% 3.21/0.80    ~spl5_54 | spl5_1 | ~spl5_3 | spl5_7 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f201,f118,f98,f78,f68,f470])).
% 3.21/0.80  fof(f470,plain,(
% 3.21/0.80    spl5_54 <=> v2_struct_0(k2_tsep_1(sK0,sK4,sK4))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 3.21/0.80  fof(f201,plain,(
% 3.21/0.80    ~v2_struct_0(k2_tsep_1(sK0,sK4,sK4)) | (spl5_1 | ~spl5_3 | spl5_7 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f100,f120,f65])).
% 3.21/0.80  fof(f65,plain,(
% 3.21/0.80    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.21/0.80    inference(cnf_transformation,[],[f27])).
% 3.21/0.80  fof(f468,plain,(
% 3.21/0.80    ~spl5_53 | spl5_1 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f200,f118,f113,f98,f93,f78,f68,f465])).
% 3.21/0.80  fof(f465,plain,(
% 3.21/0.80    spl5_53 <=> v2_struct_0(k2_tsep_1(sK0,sK3,sK4))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 3.21/0.80  fof(f200,plain,(
% 3.21/0.80    ~v2_struct_0(k2_tsep_1(sK0,sK3,sK4)) | (spl5_1 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f100,f120,f65])).
% 3.21/0.80  fof(f463,plain,(
% 3.21/0.80    ~spl5_52 | spl5_1 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f199,f118,f108,f98,f88,f78,f68,f460])).
% 3.21/0.80  fof(f199,plain,(
% 3.21/0.80    ~v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) | (spl5_1 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f100,f120,f65])).
% 3.21/0.80  fof(f458,plain,(
% 3.21/0.80    ~spl5_51 | spl5_1 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11),
% 3.21/0.80    inference(avatar_split_clause,[],[f198,f118,f103,f98,f83,f78,f68,f455])).
% 3.21/0.80  fof(f455,plain,(
% 3.21/0.80    spl5_51 <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK4))),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 3.21/0.80  fof(f198,plain,(
% 3.21/0.80    ~v2_struct_0(k2_tsep_1(sK0,sK1,sK4)) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f100,f120,f65])).
% 3.21/0.80  fof(f445,plain,(
% 3.21/0.80    ~spl5_50 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_6 | spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_13 | spl5_47),
% 3.21/0.80    inference(avatar_split_clause,[],[f428,f422,f128,f118,f113,f108,f98,f93,f88,f78,f73,f68,f442])).
% 3.21/0.80  fof(f442,plain,(
% 3.21/0.80    spl5_50 <=> r1_tsep_1(sK4,sK2)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 3.21/0.80  fof(f428,plain,(
% 3.21/0.80    ~r1_tsep_1(sK4,sK2) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_6 | spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_13 | spl5_47)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f75,f80,f95,f90,f100,f115,f120,f110,f130,f423,f54])).
% 3.21/0.80  fof(f54,plain,(
% 3.21/0.80    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | r1_tsep_1(X1,X3) | v2_struct_0(X0)) )),
% 3.21/0.80    inference(cnf_transformation,[],[f19])).
% 3.21/0.80  fof(f438,plain,(
% 3.21/0.80    spl5_49 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_6 | spl5_7 | ~spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_13 | ~spl5_43),
% 3.21/0.80    inference(avatar_split_clause,[],[f416,f396,f128,f118,f113,f103,f98,f93,f83,f78,f73,f68,f435])).
% 3.21/0.80  fof(f435,plain,(
% 3.21/0.80    spl5_49 <=> r1_tsep_1(sK3,sK1)),
% 3.21/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 3.21/0.80  fof(f416,plain,(
% 3.21/0.80    r1_tsep_1(sK3,sK1) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_6 | spl5_7 | ~spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_13 | ~spl5_43)),
% 3.21/0.80    inference(unit_resulting_resolution,[],[f70,f100,f80,f95,f115,f130,f85,f120,f398,f105,f75,f55])).
% 3.21/0.80  fof(f398,plain,(
% 3.21/0.80    r1_tsep_1(sK1,sK4) | ~spl5_43),
% 3.21/0.80    inference(avatar_component_clause,[],[f396])).
% 3.62/0.80  fof(f433,plain,(
% 3.62/0.80    ~spl5_48 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11 | spl5_15 | ~spl5_43),
% 3.62/0.80    inference(avatar_split_clause,[],[f415,f396,f137,f118,f103,f98,f83,f78,f73,f68,f430])).
% 3.62/0.80  fof(f430,plain,(
% 3.62/0.80    spl5_48 <=> m1_pre_topc(sK4,sK4)),
% 3.62/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 3.62/0.80  fof(f415,plain,(
% 3.62/0.80    ~m1_pre_topc(sK4,sK4) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11 | spl5_15 | ~spl5_43)),
% 3.62/0.80    inference(unit_resulting_resolution,[],[f70,f100,f80,f139,f120,f100,f85,f120,f398,f105,f75,f55])).
% 3.62/0.80  fof(f425,plain,(
% 3.62/0.80    spl5_47 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_6 | spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_13 | ~spl5_16),
% 3.62/0.80    inference(avatar_split_clause,[],[f417,f142,f128,f118,f113,f108,f98,f93,f88,f78,f73,f68,f422])).
% 3.62/0.80  fof(f417,plain,(
% 3.62/0.80    r1_tsep_1(sK3,sK2) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_6 | spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_13 | ~spl5_16)),
% 3.62/0.80    inference(unit_resulting_resolution,[],[f70,f100,f80,f95,f115,f130,f90,f120,f144,f110,f75,f55])).
% 3.62/0.80  fof(f414,plain,(
% 3.62/0.80    ~spl5_46 | spl5_1 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11),
% 3.62/0.80    inference(avatar_split_clause,[],[f197,f118,f113,f98,f93,f78,f68,f411])).
% 3.62/0.80  fof(f411,plain,(
% 3.62/0.80    spl5_46 <=> v2_struct_0(k2_tsep_1(sK0,sK4,sK3))),
% 3.62/0.80    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 3.62/0.80  fof(f197,plain,(
% 3.62/0.80    ~v2_struct_0(k2_tsep_1(sK0,sK4,sK3)) | (spl5_1 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11)),
% 3.62/0.80    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f95,f115,f65])).
% 3.62/0.80  fof(f409,plain,(
% 3.62/0.80    ~spl5_45 | spl5_1 | ~spl5_3 | spl5_6 | ~spl5_10),
% 3.62/0.80    inference(avatar_split_clause,[],[f196,f113,f93,f78,f68,f406])).
% 3.62/0.81  fof(f406,plain,(
% 3.62/0.81    spl5_45 <=> v2_struct_0(k2_tsep_1(sK0,sK3,sK3))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 3.62/0.81  fof(f196,plain,(
% 3.62/0.81    ~v2_struct_0(k2_tsep_1(sK0,sK3,sK3)) | (spl5_1 | ~spl5_3 | spl5_6 | ~spl5_10)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f95,f115,f65])).
% 3.62/0.81  fof(f404,plain,(
% 3.62/0.81    ~spl5_44 | spl5_1 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10),
% 3.62/0.81    inference(avatar_split_clause,[],[f195,f113,f108,f93,f88,f78,f68,f401])).
% 3.62/0.81  fof(f401,plain,(
% 3.62/0.81    spl5_44 <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK3))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 3.62/0.81  fof(f195,plain,(
% 3.62/0.81    ~v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) | (spl5_1 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f95,f115,f65])).
% 3.62/0.81  fof(f399,plain,(
% 3.62/0.81    spl5_43 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_5 | spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_12 | ~spl5_16),
% 3.62/0.81    inference(avatar_split_clause,[],[f391,f142,f123,f118,f108,f103,f98,f88,f83,f78,f73,f68,f396])).
% 3.62/0.81  fof(f391,plain,(
% 3.62/0.81    r1_tsep_1(sK1,sK4) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | spl5_5 | spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_12 | ~spl5_16)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f90,f80,f85,f105,f125,f100,f110,f144,f120,f75,f54])).
% 3.62/0.81  fof(f390,plain,(
% 3.62/0.81    ~spl5_42 | spl5_1 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10),
% 3.62/0.81    inference(avatar_split_clause,[],[f194,f113,f103,f93,f83,f78,f68,f387])).
% 3.62/0.81  fof(f387,plain,(
% 3.62/0.81    spl5_42 <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK3))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 3.62/0.81  fof(f194,plain,(
% 3.62/0.81    ~v2_struct_0(k2_tsep_1(sK0,sK1,sK3)) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f95,f115,f65])).
% 3.62/0.81  fof(f385,plain,(
% 3.62/0.81    ~spl5_41 | spl5_1 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11),
% 3.62/0.81    inference(avatar_split_clause,[],[f193,f118,f108,f98,f88,f78,f68,f382])).
% 3.62/0.81  fof(f382,plain,(
% 3.62/0.81    spl5_41 <=> v2_struct_0(k2_tsep_1(sK0,sK4,sK2))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 3.62/0.81  fof(f193,plain,(
% 3.62/0.81    ~v2_struct_0(k2_tsep_1(sK0,sK4,sK2)) | (spl5_1 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f90,f110,f65])).
% 3.62/0.81  fof(f380,plain,(
% 3.62/0.81    ~spl5_40 | spl5_1 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10),
% 3.62/0.81    inference(avatar_split_clause,[],[f192,f113,f108,f93,f88,f78,f68,f377])).
% 3.62/0.81  fof(f377,plain,(
% 3.62/0.81    spl5_40 <=> v2_struct_0(k2_tsep_1(sK0,sK3,sK2))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 3.62/0.81  fof(f192,plain,(
% 3.62/0.81    ~v2_struct_0(k2_tsep_1(sK0,sK3,sK2)) | (spl5_1 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f90,f110,f65])).
% 3.62/0.81  fof(f375,plain,(
% 3.62/0.81    ~spl5_39 | spl5_1 | ~spl5_3 | spl5_5 | ~spl5_9),
% 3.62/0.81    inference(avatar_split_clause,[],[f191,f108,f88,f78,f68,f372])).
% 3.62/0.81  fof(f372,plain,(
% 3.62/0.81    spl5_39 <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK2))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 3.62/0.81  fof(f191,plain,(
% 3.62/0.81    ~v2_struct_0(k2_tsep_1(sK0,sK2,sK2)) | (spl5_1 | ~spl5_3 | spl5_5 | ~spl5_9)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f90,f110,f65])).
% 3.62/0.81  fof(f370,plain,(
% 3.62/0.81    ~spl5_38 | spl5_1 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9),
% 3.62/0.81    inference(avatar_split_clause,[],[f190,f108,f103,f88,f83,f78,f68,f367])).
% 3.62/0.81  fof(f367,plain,(
% 3.62/0.81    spl5_38 <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 3.62/0.81  fof(f190,plain,(
% 3.62/0.81    ~v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f90,f110,f65])).
% 3.62/0.81  fof(f329,plain,(
% 3.62/0.81    ~spl5_37 | spl5_1 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11),
% 3.62/0.81    inference(avatar_split_clause,[],[f189,f118,f103,f98,f83,f78,f68,f326])).
% 3.62/0.81  fof(f326,plain,(
% 3.62/0.81    spl5_37 <=> v2_struct_0(k2_tsep_1(sK0,sK4,sK1))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 3.62/0.81  fof(f189,plain,(
% 3.62/0.81    ~v2_struct_0(k2_tsep_1(sK0,sK4,sK1)) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f85,f105,f65])).
% 3.62/0.81  fof(f324,plain,(
% 3.62/0.81    ~spl5_36 | spl5_1 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10),
% 3.62/0.81    inference(avatar_split_clause,[],[f188,f113,f103,f93,f83,f78,f68,f321])).
% 3.62/0.81  fof(f321,plain,(
% 3.62/0.81    spl5_36 <=> v2_struct_0(k2_tsep_1(sK0,sK3,sK1))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 3.62/0.81  fof(f188,plain,(
% 3.62/0.81    ~v2_struct_0(k2_tsep_1(sK0,sK3,sK1)) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f85,f105,f65])).
% 3.62/0.81  fof(f319,plain,(
% 3.62/0.81    ~spl5_35 | spl5_1 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9),
% 3.62/0.81    inference(avatar_split_clause,[],[f187,f108,f103,f88,f83,f78,f68,f316])).
% 3.62/0.81  fof(f316,plain,(
% 3.62/0.81    spl5_35 <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK1))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 3.62/0.81  fof(f187,plain,(
% 3.62/0.81    ~v2_struct_0(k2_tsep_1(sK0,sK2,sK1)) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f85,f105,f65])).
% 3.62/0.81  fof(f314,plain,(
% 3.62/0.81    ~spl5_34 | spl5_1 | ~spl5_3 | spl5_4 | ~spl5_8),
% 3.62/0.81    inference(avatar_split_clause,[],[f186,f103,f83,f78,f68,f311])).
% 3.62/0.81  fof(f311,plain,(
% 3.62/0.81    spl5_34 <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK1))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 3.62/0.81  fof(f186,plain,(
% 3.62/0.81    ~v2_struct_0(k2_tsep_1(sK0,sK1,sK1)) | (spl5_1 | ~spl5_3 | spl5_4 | ~spl5_8)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f85,f105,f65])).
% 3.62/0.81  fof(f293,plain,(
% 3.62/0.81    ~spl5_33 | spl5_1 | ~spl5_3 | spl5_7 | ~spl5_11),
% 3.62/0.81    inference(avatar_split_clause,[],[f165,f118,f98,f78,f68,f290])).
% 3.62/0.81  fof(f290,plain,(
% 3.62/0.81    spl5_33 <=> v2_struct_0(k1_tsep_1(sK0,sK4,sK4))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 3.62/0.81  fof(f165,plain,(
% 3.62/0.81    ~v2_struct_0(k1_tsep_1(sK0,sK4,sK4)) | (spl5_1 | ~spl5_3 | spl5_7 | ~spl5_11)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f100,f120,f63])).
% 3.62/0.81  fof(f63,plain,(
% 3.62/0.81    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/0.81    inference(cnf_transformation,[],[f25])).
% 3.62/0.81  fof(f288,plain,(
% 3.62/0.81    ~spl5_32 | spl5_1 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11),
% 3.62/0.81    inference(avatar_split_clause,[],[f164,f118,f113,f98,f93,f78,f68,f285])).
% 3.62/0.81  fof(f285,plain,(
% 3.62/0.81    spl5_32 <=> v2_struct_0(k1_tsep_1(sK0,sK3,sK4))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 3.62/0.81  fof(f164,plain,(
% 3.62/0.81    ~v2_struct_0(k1_tsep_1(sK0,sK3,sK4)) | (spl5_1 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f100,f120,f63])).
% 3.62/0.81  fof(f267,plain,(
% 3.62/0.81    ~spl5_31 | spl5_1 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11),
% 3.62/0.81    inference(avatar_split_clause,[],[f163,f118,f108,f98,f88,f78,f68,f264])).
% 3.62/0.81  fof(f264,plain,(
% 3.62/0.81    spl5_31 <=> v2_struct_0(k1_tsep_1(sK0,sK2,sK4))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 3.62/0.81  fof(f163,plain,(
% 3.62/0.81    ~v2_struct_0(k1_tsep_1(sK0,sK2,sK4)) | (spl5_1 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f100,f120,f63])).
% 3.62/0.81  fof(f262,plain,(
% 3.62/0.81    ~spl5_30 | spl5_1 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11),
% 3.62/0.81    inference(avatar_split_clause,[],[f162,f118,f103,f98,f83,f78,f68,f259])).
% 3.62/0.81  fof(f259,plain,(
% 3.62/0.81    spl5_30 <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK4))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 3.62/0.81  fof(f162,plain,(
% 3.62/0.81    ~v2_struct_0(k1_tsep_1(sK0,sK1,sK4)) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f100,f120,f63])).
% 3.62/0.81  fof(f257,plain,(
% 3.62/0.81    ~spl5_29 | spl5_1 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11),
% 3.62/0.81    inference(avatar_split_clause,[],[f161,f118,f113,f98,f93,f78,f68,f254])).
% 3.62/0.81  fof(f254,plain,(
% 3.62/0.81    spl5_29 <=> v2_struct_0(k1_tsep_1(sK0,sK4,sK3))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 3.62/0.81  fof(f161,plain,(
% 3.62/0.81    ~v2_struct_0(k1_tsep_1(sK0,sK4,sK3)) | (spl5_1 | ~spl5_3 | spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f95,f115,f63])).
% 3.62/0.81  fof(f252,plain,(
% 3.62/0.81    ~spl5_28 | spl5_1 | ~spl5_3 | spl5_6 | ~spl5_10),
% 3.62/0.81    inference(avatar_split_clause,[],[f160,f113,f93,f78,f68,f249])).
% 3.62/0.81  fof(f249,plain,(
% 3.62/0.81    spl5_28 <=> v2_struct_0(k1_tsep_1(sK0,sK3,sK3))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 3.62/0.81  fof(f160,plain,(
% 3.62/0.81    ~v2_struct_0(k1_tsep_1(sK0,sK3,sK3)) | (spl5_1 | ~spl5_3 | spl5_6 | ~spl5_10)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f95,f115,f63])).
% 3.62/0.81  fof(f247,plain,(
% 3.62/0.81    ~spl5_27 | spl5_1 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10),
% 3.62/0.81    inference(avatar_split_clause,[],[f159,f113,f108,f93,f88,f78,f68,f244])).
% 3.62/0.81  fof(f244,plain,(
% 3.62/0.81    spl5_27 <=> v2_struct_0(k1_tsep_1(sK0,sK2,sK3))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 3.62/0.81  fof(f159,plain,(
% 3.62/0.81    ~v2_struct_0(k1_tsep_1(sK0,sK2,sK3)) | (spl5_1 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f95,f115,f63])).
% 3.62/0.81  fof(f226,plain,(
% 3.62/0.81    ~spl5_26 | spl5_1 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10),
% 3.62/0.81    inference(avatar_split_clause,[],[f158,f113,f103,f93,f83,f78,f68,f223])).
% 3.62/0.81  fof(f158,plain,(
% 3.62/0.81    ~v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f95,f115,f63])).
% 3.62/0.81  fof(f221,plain,(
% 3.62/0.81    ~spl5_25 | spl5_1 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11),
% 3.62/0.81    inference(avatar_split_clause,[],[f157,f118,f108,f98,f88,f78,f68,f218])).
% 3.62/0.81  fof(f218,plain,(
% 3.62/0.81    spl5_25 <=> v2_struct_0(k1_tsep_1(sK0,sK4,sK2))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 3.62/0.81  fof(f157,plain,(
% 3.62/0.81    ~v2_struct_0(k1_tsep_1(sK0,sK4,sK2)) | (spl5_1 | ~spl5_3 | spl5_5 | spl5_7 | ~spl5_9 | ~spl5_11)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f90,f110,f63])).
% 3.62/0.81  fof(f216,plain,(
% 3.62/0.81    ~spl5_24 | spl5_1 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10),
% 3.62/0.81    inference(avatar_split_clause,[],[f156,f113,f108,f93,f88,f78,f68,f213])).
% 3.62/0.81  fof(f213,plain,(
% 3.62/0.81    spl5_24 <=> v2_struct_0(k1_tsep_1(sK0,sK3,sK2))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 3.62/0.81  fof(f156,plain,(
% 3.62/0.81    ~v2_struct_0(k1_tsep_1(sK0,sK3,sK2)) | (spl5_1 | ~spl5_3 | spl5_5 | spl5_6 | ~spl5_9 | ~spl5_10)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f90,f110,f63])).
% 3.62/0.81  fof(f211,plain,(
% 3.62/0.81    ~spl5_23 | spl5_1 | ~spl5_3 | spl5_5 | ~spl5_9),
% 3.62/0.81    inference(avatar_split_clause,[],[f155,f108,f88,f78,f68,f208])).
% 3.62/0.81  fof(f208,plain,(
% 3.62/0.81    spl5_23 <=> v2_struct_0(k1_tsep_1(sK0,sK2,sK2))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 3.62/0.81  fof(f155,plain,(
% 3.62/0.81    ~v2_struct_0(k1_tsep_1(sK0,sK2,sK2)) | (spl5_1 | ~spl5_3 | spl5_5 | ~spl5_9)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f90,f110,f63])).
% 3.62/0.81  fof(f206,plain,(
% 3.62/0.81    ~spl5_22 | spl5_1 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9),
% 3.62/0.81    inference(avatar_split_clause,[],[f154,f108,f103,f88,f83,f78,f68,f203])).
% 3.62/0.81  fof(f203,plain,(
% 3.62/0.81    spl5_22 <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 3.62/0.81  fof(f154,plain,(
% 3.62/0.81    ~v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f90,f110,f63])).
% 3.62/0.81  fof(f185,plain,(
% 3.62/0.81    ~spl5_21 | spl5_1 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11),
% 3.62/0.81    inference(avatar_split_clause,[],[f153,f118,f103,f98,f83,f78,f68,f182])).
% 3.62/0.81  fof(f182,plain,(
% 3.62/0.81    spl5_21 <=> v2_struct_0(k1_tsep_1(sK0,sK4,sK1))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 3.62/0.81  fof(f153,plain,(
% 3.62/0.81    ~v2_struct_0(k1_tsep_1(sK0,sK4,sK1)) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_7 | ~spl5_8 | ~spl5_11)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f100,f120,f85,f105,f63])).
% 3.62/0.81  fof(f180,plain,(
% 3.62/0.81    ~spl5_20 | spl5_1 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10),
% 3.62/0.81    inference(avatar_split_clause,[],[f152,f113,f103,f93,f83,f78,f68,f177])).
% 3.62/0.81  fof(f177,plain,(
% 3.62/0.81    spl5_20 <=> v2_struct_0(k1_tsep_1(sK0,sK3,sK1))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 3.62/0.81  fof(f152,plain,(
% 3.62/0.81    ~v2_struct_0(k1_tsep_1(sK0,sK3,sK1)) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_6 | ~spl5_8 | ~spl5_10)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f95,f115,f85,f105,f63])).
% 3.62/0.81  fof(f175,plain,(
% 3.62/0.81    ~spl5_19 | spl5_1 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9),
% 3.62/0.81    inference(avatar_split_clause,[],[f151,f108,f103,f88,f83,f78,f68,f172])).
% 3.62/0.81  fof(f172,plain,(
% 3.62/0.81    spl5_19 <=> v2_struct_0(k1_tsep_1(sK0,sK2,sK1))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 3.62/0.81  fof(f151,plain,(
% 3.62/0.81    ~v2_struct_0(k1_tsep_1(sK0,sK2,sK1)) | (spl5_1 | ~spl5_3 | spl5_4 | spl5_5 | ~spl5_8 | ~spl5_9)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f90,f110,f85,f105,f63])).
% 3.62/0.81  fof(f170,plain,(
% 3.62/0.81    ~spl5_18 | spl5_1 | ~spl5_3 | spl5_4 | ~spl5_8),
% 3.62/0.81    inference(avatar_split_clause,[],[f150,f103,f83,f78,f68,f167])).
% 3.62/0.81  fof(f167,plain,(
% 3.62/0.81    spl5_18 <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK1))),
% 3.62/0.81    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 3.62/0.81  fof(f150,plain,(
% 3.62/0.81    ~v2_struct_0(k1_tsep_1(sK0,sK1,sK1)) | (spl5_1 | ~spl5_3 | spl5_4 | ~spl5_8)),
% 3.62/0.81    inference(unit_resulting_resolution,[],[f70,f80,f85,f105,f85,f105,f63])).
% 3.62/0.81  fof(f149,plain,(
% 3.62/0.81    spl5_16 | spl5_17),
% 3.62/0.81    inference(avatar_split_clause,[],[f47,f146,f142])).
% 3.62/0.81  fof(f47,plain,(
% 3.62/0.81    r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(sK2,sK4)),
% 3.62/0.81    inference(cnf_transformation,[],[f33])).
% 3.62/0.81  fof(f33,plain,(
% 3.62/0.81    (((((~r1_tsep_1(sK4,sK1) | ~r1_tsep_1(sK2,sK3)) & (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(sK2,sK4)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.62/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f32,f31,f30,f29,f28])).
% 3.62/0.81  fof(f28,plain,(
% 3.62/0.81    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.62/0.81    introduced(choice_axiom,[])).
% 3.62/0.81  fof(f29,plain,(
% 3.62/0.81    ? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,sK1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,sK1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(sK1,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 3.62/0.81    introduced(choice_axiom,[])).
% 3.62/0.81  fof(f30,plain,(
% 3.62/0.81    ? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,sK1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,sK1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(sK1,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : ((~r1_tsep_1(X4,sK1) | ~r1_tsep_1(sK2,X3)) & (r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,X3)) | r1_tsep_1(sK2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 3.62/0.81    introduced(choice_axiom,[])).
% 3.62/0.81  fof(f31,plain,(
% 3.62/0.81    ? [X3] : (? [X4] : ((~r1_tsep_1(X4,sK1) | ~r1_tsep_1(sK2,X3)) & (r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,X3)) | r1_tsep_1(sK2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : ((~r1_tsep_1(X4,sK1) | ~r1_tsep_1(sK2,sK3)) & (r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(sK2,X4)) & m1_pre_topc(sK3,X4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 3.62/0.81    introduced(choice_axiom,[])).
% 3.62/0.81  fof(f32,plain,(
% 3.62/0.81    ? [X4] : ((~r1_tsep_1(X4,sK1) | ~r1_tsep_1(sK2,sK3)) & (r1_tsep_1(k2_tsep_1(sK0,sK2,X4),k1_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(sK2,X4)) & m1_pre_topc(sK3,X4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) => ((~r1_tsep_1(sK4,sK1) | ~r1_tsep_1(sK2,sK3)) & (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(sK2,sK4)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4))),
% 3.62/0.81    introduced(choice_axiom,[])).
% 3.62/0.81  fof(f13,plain,(
% 3.62/0.81    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.62/0.81    inference(flattening,[],[f12])).
% 3.62/0.81  fof(f12,plain,(
% 3.62/0.81    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4))) & (m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.62/0.81    inference(ennf_transformation,[],[f9])).
% 3.62/0.81  fof(f9,negated_conjecture,(
% 3.62/0.81    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2)) => ((r1_tsep_1(X4,X1) & r1_tsep_1(X2,X3)) | (~r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) & ~r1_tsep_1(X2,X4)))))))))),
% 3.62/0.81    inference(negated_conjecture,[],[f8])).
% 3.62/0.81  fof(f8,conjecture,(
% 3.62/0.81    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2)) => ((r1_tsep_1(X4,X1) & r1_tsep_1(X2,X3)) | (~r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) & ~r1_tsep_1(X2,X4)))))))))),
% 3.62/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tmap_1)).
% 3.62/0.81  fof(f140,plain,(
% 3.62/0.81    ~spl5_14 | ~spl5_15),
% 3.62/0.81    inference(avatar_split_clause,[],[f48,f137,f133])).
% 3.62/0.81  fof(f48,plain,(
% 3.62/0.81    ~r1_tsep_1(sK4,sK1) | ~r1_tsep_1(sK2,sK3)),
% 3.62/0.81    inference(cnf_transformation,[],[f33])).
% 3.62/0.81  fof(f131,plain,(
% 3.62/0.81    spl5_13),
% 3.62/0.81    inference(avatar_split_clause,[],[f46,f128])).
% 3.62/0.81  fof(f46,plain,(
% 3.62/0.81    m1_pre_topc(sK3,sK4)),
% 3.62/0.81    inference(cnf_transformation,[],[f33])).
% 3.62/0.81  fof(f126,plain,(
% 3.62/0.81    spl5_12),
% 3.62/0.81    inference(avatar_split_clause,[],[f45,f123])).
% 3.62/0.81  fof(f45,plain,(
% 3.62/0.81    m1_pre_topc(sK1,sK2)),
% 3.62/0.81    inference(cnf_transformation,[],[f33])).
% 3.62/0.81  fof(f121,plain,(
% 3.62/0.81    spl5_11),
% 3.62/0.81    inference(avatar_split_clause,[],[f44,f118])).
% 3.62/0.81  fof(f44,plain,(
% 3.62/0.81    m1_pre_topc(sK4,sK0)),
% 3.62/0.81    inference(cnf_transformation,[],[f33])).
% 3.62/0.81  fof(f116,plain,(
% 3.62/0.81    spl5_10),
% 3.62/0.81    inference(avatar_split_clause,[],[f42,f113])).
% 3.62/0.81  fof(f42,plain,(
% 3.62/0.81    m1_pre_topc(sK3,sK0)),
% 3.62/0.81    inference(cnf_transformation,[],[f33])).
% 3.62/0.81  fof(f111,plain,(
% 3.62/0.81    spl5_9),
% 3.62/0.81    inference(avatar_split_clause,[],[f40,f108])).
% 3.62/0.81  fof(f40,plain,(
% 3.62/0.81    m1_pre_topc(sK2,sK0)),
% 3.62/0.81    inference(cnf_transformation,[],[f33])).
% 3.62/0.81  fof(f106,plain,(
% 3.62/0.81    spl5_8),
% 3.62/0.81    inference(avatar_split_clause,[],[f38,f103])).
% 3.62/0.81  fof(f38,plain,(
% 3.62/0.81    m1_pre_topc(sK1,sK0)),
% 3.62/0.81    inference(cnf_transformation,[],[f33])).
% 3.62/0.81  fof(f101,plain,(
% 3.62/0.81    ~spl5_7),
% 3.62/0.81    inference(avatar_split_clause,[],[f43,f98])).
% 3.62/0.81  fof(f43,plain,(
% 3.62/0.81    ~v2_struct_0(sK4)),
% 3.62/0.81    inference(cnf_transformation,[],[f33])).
% 3.62/0.81  fof(f96,plain,(
% 3.62/0.81    ~spl5_6),
% 3.62/0.81    inference(avatar_split_clause,[],[f41,f93])).
% 3.62/0.81  fof(f41,plain,(
% 3.62/0.81    ~v2_struct_0(sK3)),
% 3.62/0.81    inference(cnf_transformation,[],[f33])).
% 3.62/0.81  fof(f91,plain,(
% 3.62/0.81    ~spl5_5),
% 3.62/0.81    inference(avatar_split_clause,[],[f39,f88])).
% 3.62/0.81  fof(f39,plain,(
% 3.62/0.81    ~v2_struct_0(sK2)),
% 3.62/0.81    inference(cnf_transformation,[],[f33])).
% 3.62/0.81  fof(f86,plain,(
% 3.62/0.81    ~spl5_4),
% 3.62/0.81    inference(avatar_split_clause,[],[f37,f83])).
% 3.62/0.81  fof(f37,plain,(
% 3.62/0.81    ~v2_struct_0(sK1)),
% 3.62/0.81    inference(cnf_transformation,[],[f33])).
% 3.62/0.81  fof(f81,plain,(
% 3.62/0.81    spl5_3),
% 3.62/0.81    inference(avatar_split_clause,[],[f36,f78])).
% 3.62/0.81  fof(f36,plain,(
% 3.62/0.81    l1_pre_topc(sK0)),
% 3.62/0.81    inference(cnf_transformation,[],[f33])).
% 3.62/0.81  fof(f76,plain,(
% 3.62/0.81    spl5_2),
% 3.62/0.81    inference(avatar_split_clause,[],[f35,f73])).
% 3.62/0.81  fof(f35,plain,(
% 3.62/0.81    v2_pre_topc(sK0)),
% 3.62/0.81    inference(cnf_transformation,[],[f33])).
% 3.62/0.81  fof(f71,plain,(
% 3.62/0.81    ~spl5_1),
% 3.62/0.81    inference(avatar_split_clause,[],[f34,f68])).
% 3.62/0.81  fof(f34,plain,(
% 3.62/0.81    ~v2_struct_0(sK0)),
% 3.62/0.81    inference(cnf_transformation,[],[f33])).
% 3.62/0.81  % SZS output end Proof for theBenchmark
% 3.62/0.81  % (13372)------------------------------
% 3.62/0.81  % (13372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.62/0.81  % (13372)Termination reason: Refutation
% 3.62/0.81  
% 3.62/0.81  % (13372)Memory used [KB]: 8699
% 3.62/0.81  % (13372)Time elapsed: 0.382 s
% 3.62/0.81  % (13372)------------------------------
% 3.62/0.81  % (13372)------------------------------
% 3.62/0.81  % (13371)Success in time 0.458 s
%------------------------------------------------------------------------------
