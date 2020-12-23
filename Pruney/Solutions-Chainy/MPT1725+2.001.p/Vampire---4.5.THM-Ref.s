%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:07 EST 2020

% Result     : Theorem 2.25s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 908 expanded)
%              Number of leaves         :   55 ( 510 expanded)
%              Depth                    :    7
%              Number of atoms          : 1213 (5162 expanded)
%              Number of equality atoms :   16 (  37 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4210,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f108,f113,f114,f119,f124,f129,f134,f139,f144,f149,f154,f159,f164,f188,f199,f231,f263,f268,f278,f323,f328,f338,f379,f390,f450,f456,f463,f535,f810,f1011,f1081,f2952,f3581,f3624,f3677,f3828,f3900,f4164,f4165,f4209])).

fof(f4209,plain,
    ( spl5_116
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_21
    | spl5_50 ),
    inference(avatar_split_clause,[],[f910,f376,f194,f161,f156,f151,f146,f141,f126,f121,f807])).

fof(f807,plain,
    ( spl5_116
  <=> k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).

fof(f121,plain,
    ( spl5_8
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f126,plain,
    ( spl5_9
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f141,plain,
    ( spl5_12
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f146,plain,
    ( spl5_13
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f151,plain,
    ( spl5_14
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f156,plain,
    ( spl5_15
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f161,plain,
    ( spl5_16
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f194,plain,
    ( spl5_21
  <=> sP4(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f376,plain,
    ( spl5_50
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f910,plain,
    ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3)
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_21
    | spl5_50 ),
    inference(unit_resulting_resolution,[],[f196,f163,f158,f153,f128,f148,f123,f143,f378,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X1,X2)
      | k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP4(X0) ) ),
    inference(general_splitting,[],[f66,f85_D])).

fof(f85,plain,(
    ! [X0,X3] :
      ( sP4(X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0) ) ),
    inference(cnf_transformation,[],[f85_D])).

fof(f85_D,plain,(
    ! [X0] :
      ( ! [X3] :
          ( v2_struct_0(X3)
          | ~ m1_pre_topc(X3,X0) )
    <=> ~ sP4(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tsep_1)).

fof(f378,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl5_50 ),
    inference(avatar_component_clause,[],[f376])).

fof(f143,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f123,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f148,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f128,plain,
    ( ~ v2_struct_0(sK3)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f153,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f158,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f163,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f161])).

fof(f196,plain,
    ( sP4(sK0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f194])).

fof(f4165,plain,
    ( ~ spl5_48
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
    inference(avatar_split_clause,[],[f3855,f161,f156,f151,f146,f141,f136,f131,f126,f121,f116,f110,f363])).

fof(f363,plain,
    ( spl5_48
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f110,plain,
    ( spl5_6
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f116,plain,
    ( spl5_7
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f131,plain,
    ( spl5_10
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f136,plain,
    ( spl5_11
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f3855,plain,
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
    inference(unit_resulting_resolution,[],[f163,f158,f153,f138,f148,f128,f133,f123,f143,f118,f112,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X3,X1)
      | ~ r1_tsep_1(X3,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f112,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f118,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f133,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f138,plain,
    ( ~ v2_struct_0(sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f136])).

fof(f4164,plain,
    ( spl5_525
    | ~ spl5_3
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | spl5_30
    | spl5_33
    | ~ spl5_40
    | ~ spl5_43
    | ~ spl5_553 ),
    inference(avatar_split_clause,[],[f4151,f3896,f335,f320,f275,f260,f161,f156,f151,f136,f131,f96,f3673])).

fof(f3673,plain,
    ( spl5_525
  <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_525])])).

fof(f96,plain,
    ( spl5_3
  <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f260,plain,
    ( spl5_30
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f275,plain,
    ( spl5_33
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f320,plain,
    ( spl5_40
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f335,plain,
    ( spl5_43
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f3896,plain,
    ( spl5_553
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_553])])).

fof(f4151,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl5_3
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | spl5_30
    | spl5_33
    | ~ spl5_40
    | ~ spl5_43
    | ~ spl5_553 ),
    inference(unit_resulting_resolution,[],[f163,f158,f153,f138,f133,f262,f277,f322,f337,f98,f3898,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X1,X3)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3898,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ spl5_553 ),
    inference(avatar_component_clause,[],[f3896])).

fof(f98,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f337,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f335])).

fof(f322,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f320])).

fof(f277,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | spl5_33 ),
    inference(avatar_component_clause,[],[f275])).

fof(f262,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f260])).

fof(f3900,plain,
    ( spl5_553
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
    | spl5_16
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f3852,f387,f161,f156,f151,f146,f141,f136,f131,f126,f121,f116,f110,f3896])).

fof(f387,plain,
    ( spl5_52
  <=> m1_pre_topc(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f3852,plain,
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
    | spl5_16
    | ~ spl5_52 ),
    inference(unit_resulting_resolution,[],[f163,f158,f153,f148,f148,f138,f128,f143,f133,f143,f123,f389,f118,f112,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X4)
      | ~ m1_pre_topc(X1,X3)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      | r1_tsep_1(X1,X2)
                      | ~ m1_pre_topc(X2,X4)
                      | ~ m1_pre_topc(X1,X3)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
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
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      | r1_tsep_1(X1,X2)
                      | ~ m1_pre_topc(X2,X4)
                      | ~ m1_pre_topc(X1,X3)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
                     => ( ( m1_pre_topc(X2,X4)
                          & m1_pre_topc(X1,X3) )
                       => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                          | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tmap_1)).

fof(f389,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f387])).

fof(f3828,plain,
    ( spl5_512
    | ~ spl5_2
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | spl5_30
    | spl5_31
    | ~ spl5_40
    | ~ spl5_41
    | ~ spl5_160 ),
    inference(avatar_split_clause,[],[f3815,f1078,f325,f320,f265,f260,f161,f156,f151,f146,f141,f92,f3576])).

fof(f3576,plain,
    ( spl5_512
  <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_512])])).

fof(f92,plain,
    ( spl5_2
  <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f265,plain,
    ( spl5_31
  <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f325,plain,
    ( spl5_41
  <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f1078,plain,
    ( spl5_160
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_160])])).

fof(f3815,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ spl5_2
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | spl5_30
    | spl5_31
    | ~ spl5_40
    | ~ spl5_41
    | ~ spl5_160 ),
    inference(unit_resulting_resolution,[],[f163,f158,f153,f148,f143,f262,f267,f322,f327,f94,f1080,f75])).

fof(f1080,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK2,sK3))
    | ~ spl5_160 ),
    inference(avatar_component_clause,[],[f1078])).

fof(f94,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f327,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f325])).

fof(f267,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | spl5_31 ),
    inference(avatar_component_clause,[],[f265])).

fof(f3677,plain,
    ( ~ spl5_525
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | spl5_30
    | ~ spl5_40
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f3637,f453,f320,f260,f161,f156,f151,f136,f131,f3673])).

fof(f453,plain,
    ( spl5_63
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f3637,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | spl5_30
    | ~ spl5_40
    | ~ spl5_63 ),
    inference(unit_resulting_resolution,[],[f163,f158,f153,f138,f133,f262,f322,f455,f79])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f455,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f453])).

fof(f3624,plain,
    ( k2_tsep_1(sK0,sK2,sK3) != k2_tsep_1(sK0,sK3,sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3581,plain,
    ( ~ spl5_512
    | spl5_13
    | ~ spl5_20
    | ~ spl5_26
    | spl5_30
    | ~ spl5_52
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f3539,f447,f387,f260,f228,f185,f146,f3576])).

fof(f185,plain,
    ( spl5_20
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f228,plain,
    ( spl5_26
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f447,plain,
    ( spl5_62
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f3539,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1)
    | spl5_13
    | ~ spl5_20
    | ~ spl5_26
    | spl5_30
    | ~ spl5_52
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f148,f230,f187,f148,f389,f262,f449,f449,f79])).

fof(f449,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f447])).

fof(f187,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f185])).

fof(f230,plain,
    ( v2_pre_topc(sK1)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f228])).

fof(f2952,plain,
    ( spl5_3
    | ~ spl5_4
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f2951,f807,f100,f96])).

fof(f100,plain,
    ( spl5_4
  <=> r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f2951,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | ~ spl5_4
    | ~ spl5_116 ),
    inference(forward_demodulation,[],[f102,f809])).

fof(f809,plain,
    ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3)
    | ~ spl5_116 ),
    inference(avatar_component_clause,[],[f807])).

fof(f102,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f1081,plain,
    ( spl5_160
    | ~ spl5_78
    | ~ spl5_146 ),
    inference(avatar_split_clause,[],[f1071,f1008,f532,f1078])).

fof(f532,plain,
    ( spl5_78
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f1008,plain,
    ( spl5_146
  <=> k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).

fof(f1071,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK2,sK3))
    | ~ spl5_78
    | ~ spl5_146 ),
    inference(backward_demodulation,[],[f534,f1010])).

fof(f1010,plain,
    ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)
    | ~ spl5_146 ),
    inference(avatar_component_clause,[],[f1008])).

fof(f534,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | ~ spl5_78 ),
    inference(avatar_component_clause,[],[f532])).

fof(f1011,plain,
    ( spl5_146
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_21
    | spl5_64 ),
    inference(avatar_split_clause,[],[f999,f460,f194,f161,f156,f151,f136,f131,f126,f121,f1008])).

fof(f460,plain,
    ( spl5_64
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f999,plain,
    ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_21
    | spl5_64 ),
    inference(unit_resulting_resolution,[],[f196,f163,f158,f153,f128,f138,f123,f133,f462,f86])).

fof(f462,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | spl5_64 ),
    inference(avatar_component_clause,[],[f460])).

fof(f810,plain,
    ( spl5_116
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_21
    | spl5_48 ),
    inference(avatar_split_clause,[],[f798,f363,f194,f161,f156,f151,f146,f141,f126,f121,f807])).

fof(f798,plain,
    ( k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3)
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_21
    | spl5_48 ),
    inference(unit_resulting_resolution,[],[f196,f163,f158,f153,f148,f128,f143,f123,f365,f86])).

fof(f365,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | spl5_48 ),
    inference(avatar_component_clause,[],[f363])).

fof(f535,plain,
    ( spl5_78
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
    inference(avatar_split_clause,[],[f530,f161,f156,f151,f146,f141,f136,f131,f126,f121,f116,f105,f532])).

fof(f105,plain,
    ( spl5_5
  <=> m1_pre_topc(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f530,plain,
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
    inference(unit_resulting_resolution,[],[f163,f158,f153,f148,f128,f138,f143,f133,f123,f118,f107,f64])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tmap_1)).

fof(f107,plain,
    ( m1_pre_topc(sK1,sK3)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f463,plain,
    ( ~ spl5_64
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
    inference(avatar_split_clause,[],[f457,f161,f156,f151,f146,f141,f136,f131,f126,f121,f116,f105,f460])).

fof(f457,plain,
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
    inference(unit_resulting_resolution,[],[f163,f158,f153,f148,f138,f128,f143,f123,f133,f107,f118,f75])).

fof(f456,plain,
    ( spl5_63
    | spl5_7
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(avatar_split_clause,[],[f451,f161,f156,f151,f146,f141,f136,f131,f116,f453])).

fof(f451,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | spl5_7
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f163,f158,f153,f148,f138,f143,f133,f118,f74])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tsep_1)).

fof(f450,plain,
    ( spl5_62
    | spl5_7
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(avatar_split_clause,[],[f445,f161,f156,f151,f146,f141,f136,f131,f116,f447])).

fof(f445,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | spl5_7
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f163,f158,f153,f148,f138,f143,f133,f118,f73])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f390,plain,
    ( spl5_52
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f385,f185,f387])).

fof(f385,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f187,f84])).

fof(f84,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f379,plain,
    ( ~ spl5_50
    | ~ spl5_5
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(avatar_split_clause,[],[f372,f161,f156,f151,f146,f141,f126,f121,f105,f376])).

fof(f372,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ spl5_5
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f163,f128,f153,f148,f143,f107,f123,f158,f80])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f338,plain,
    ( spl5_43
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | spl5_16 ),
    inference(avatar_split_clause,[],[f303,f161,f151,f146,f141,f126,f121,f335])).

fof(f303,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f163,f153,f148,f143,f128,f123,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f328,plain,
    ( spl5_41
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | spl5_16 ),
    inference(avatar_split_clause,[],[f305,f161,f151,f136,f131,f126,f121,f325])).

fof(f305,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f163,f153,f138,f133,f128,f123,f62])).

fof(f323,plain,
    ( spl5_40
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | spl5_16 ),
    inference(avatar_split_clause,[],[f306,f161,f151,f146,f141,f136,f131,f320])).

fof(f306,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f163,f153,f148,f143,f138,f133,f62])).

fof(f278,plain,
    ( ~ spl5_33
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | spl5_16 ),
    inference(avatar_split_clause,[],[f243,f161,f151,f146,f141,f126,f121,f275])).

fof(f243,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | ~ spl5_8
    | spl5_9
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f163,f153,f148,f143,f128,f123,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f268,plain,
    ( ~ spl5_31
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | spl5_16 ),
    inference(avatar_split_clause,[],[f245,f161,f151,f136,f131,f126,f121,f265])).

fof(f245,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_14
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f163,f153,f138,f133,f128,f123,f61])).

fof(f263,plain,
    ( ~ spl5_30
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | spl5_16 ),
    inference(avatar_split_clause,[],[f246,f161,f151,f146,f141,f136,f131,f260])).

fof(f246,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_14
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f163,f153,f148,f143,f138,f133,f61])).

fof(f231,plain,
    ( spl5_26
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f214,f156,f151,f141,f228])).

fof(f214,plain,
    ( v2_pre_topc(sK1)
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f158,f153,f143,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f199,plain,
    ( spl5_21
    | ~ spl5_12
    | spl5_13 ),
    inference(avatar_split_clause,[],[f190,f146,f141,f194])).

fof(f190,plain,
    ( sP4(sK0)
    | ~ spl5_12
    | spl5_13 ),
    inference(unit_resulting_resolution,[],[f143,f148,f85])).

fof(f188,plain,
    ( spl5_20
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f171,f151,f141,f185])).

fof(f171,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f153,f143,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f164,plain,(
    ~ spl5_16 ),
    inference(avatar_split_clause,[],[f47,f161])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f45,f44,f43,f42])).

fof(f42,plain,
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

fof(f43,plain,
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

fof(f44,plain,
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

fof(f45,plain,
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tmap_1)).

fof(f159,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f48,f156])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f154,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f49,f151])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f149,plain,(
    ~ spl5_13 ),
    inference(avatar_split_clause,[],[f50,f146])).

fof(f50,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f144,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f51,f141])).

fof(f51,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f139,plain,(
    ~ spl5_11 ),
    inference(avatar_split_clause,[],[f52,f136])).

fof(f52,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f134,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f53,f131])).

fof(f53,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f129,plain,(
    ~ spl5_9 ),
    inference(avatar_split_clause,[],[f54,f126])).

fof(f54,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f124,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f55,f121])).

fof(f55,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f119,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f56,f116])).

fof(f56,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f114,plain,
    ( spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f57,f110,f105])).

fof(f57,plain,
    ( m1_pre_topc(sK2,sK3)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f113,plain,
    ( spl5_1
    | spl5_2
    | spl5_6 ),
    inference(avatar_split_clause,[],[f58,f110,f92,f88])).

fof(f88,plain,
    ( spl5_1
  <=> r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f58,plain,
    ( m1_pre_topc(sK2,sK3)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f108,plain,
    ( spl5_5
    | spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f59,f100,f96,f105])).

fof(f59,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f103,plain,
    ( spl5_1
    | spl5_2
    | spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f60,f100,f96,f92,f88])).

fof(f60,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:24:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (10382)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (10379)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (10381)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (10383)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (10388)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (10401)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  % (10392)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (10386)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (10390)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (10397)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (10396)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.52  % (10384)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (10380)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.52  % (10389)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.52  % (10378)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (10385)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.52  % (10394)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (10391)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.53  % (10395)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.53  % (10377)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.53  % (10398)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.53  % (10387)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.54  % (10399)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.55  % (10393)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.78/0.60  % (10387)Refutation not found, incomplete strategy% (10387)------------------------------
% 1.78/0.60  % (10387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.60  % (10387)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.60  
% 1.78/0.60  % (10387)Memory used [KB]: 11129
% 1.78/0.60  % (10387)Time elapsed: 0.172 s
% 1.78/0.60  % (10387)------------------------------
% 1.78/0.60  % (10387)------------------------------
% 2.25/0.71  % (10383)Refutation found. Thanks to Tanya!
% 2.25/0.71  % SZS status Theorem for theBenchmark
% 2.25/0.71  % SZS output start Proof for theBenchmark
% 2.25/0.71  fof(f4210,plain,(
% 2.25/0.71    $false),
% 2.25/0.71    inference(avatar_sat_refutation,[],[f103,f108,f113,f114,f119,f124,f129,f134,f139,f144,f149,f154,f159,f164,f188,f199,f231,f263,f268,f278,f323,f328,f338,f379,f390,f450,f456,f463,f535,f810,f1011,f1081,f2952,f3581,f3624,f3677,f3828,f3900,f4164,f4165,f4209])).
% 2.25/0.71  fof(f4209,plain,(
% 2.25/0.71    spl5_116 | ~spl5_8 | spl5_9 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_21 | spl5_50),
% 2.25/0.71    inference(avatar_split_clause,[],[f910,f376,f194,f161,f156,f151,f146,f141,f126,f121,f807])).
% 2.25/0.71  fof(f807,plain,(
% 2.25/0.71    spl5_116 <=> k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3)),
% 2.25/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).
% 2.73/0.71  fof(f121,plain,(
% 2.73/0.71    spl5_8 <=> m1_pre_topc(sK3,sK0)),
% 2.73/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.73/0.71  fof(f126,plain,(
% 2.73/0.71    spl5_9 <=> v2_struct_0(sK3)),
% 2.73/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.73/0.71  fof(f141,plain,(
% 2.73/0.71    spl5_12 <=> m1_pre_topc(sK1,sK0)),
% 2.73/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.73/0.71  fof(f146,plain,(
% 2.73/0.71    spl5_13 <=> v2_struct_0(sK1)),
% 2.73/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.73/0.71  fof(f151,plain,(
% 2.73/0.71    spl5_14 <=> l1_pre_topc(sK0)),
% 2.73/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 2.73/0.71  fof(f156,plain,(
% 2.73/0.71    spl5_15 <=> v2_pre_topc(sK0)),
% 2.73/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.73/0.71  fof(f161,plain,(
% 2.73/0.71    spl5_16 <=> v2_struct_0(sK0)),
% 2.73/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 2.73/0.71  fof(f194,plain,(
% 2.73/0.71    spl5_21 <=> sP4(sK0)),
% 2.73/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 2.73/0.71  fof(f376,plain,(
% 2.73/0.71    spl5_50 <=> r1_tsep_1(sK3,sK1)),
% 2.73/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 2.73/0.71  fof(f910,plain,(
% 2.73/0.71    k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3) | (~spl5_8 | spl5_9 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_21 | spl5_50)),
% 2.73/0.71    inference(unit_resulting_resolution,[],[f196,f163,f158,f153,f128,f148,f123,f143,f378,f86])).
% 2.73/0.71  fof(f86,plain,(
% 2.73/0.71    ( ! [X2,X0,X1] : (r1_tsep_1(X1,X2) | k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP4(X0)) )),
% 2.73/0.71    inference(general_splitting,[],[f66,f85_D])).
% 2.73/0.71  fof(f85,plain,(
% 2.73/0.71    ( ! [X0,X3] : (sP4(X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0)) )),
% 2.73/0.71    inference(cnf_transformation,[],[f85_D])).
% 2.73/0.71  fof(f85_D,plain,(
% 2.73/0.71    ( ! [X0] : (( ! [X3] : (v2_struct_0(X3) | ~m1_pre_topc(X3,X0)) ) <=> ~sP4(X0)) )),
% 2.73/0.71    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 2.73/0.71  fof(f66,plain,(
% 2.73/0.71    ( ! [X2,X0,X3,X1] : (k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.71    inference(cnf_transformation,[],[f27])).
% 2.73/0.71  fof(f27,plain,(
% 2.73/0.71    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,k2_tsep_1(X0,X1,X2),X3) = k2_tsep_1(X0,X1,k2_tsep_1(X0,X2,X3)) | ((r1_tsep_1(X1,k2_tsep_1(X0,X2,X3)) | r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))) & (k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1) | r1_tsep_1(X1,X2))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.71    inference(flattening,[],[f26])).
% 2.73/0.71  fof(f26,plain,(
% 2.73/0.71    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,k2_tsep_1(X0,X1,X2),X3) = k2_tsep_1(X0,X1,k2_tsep_1(X0,X2,X3)) | ((r1_tsep_1(X1,k2_tsep_1(X0,X2,X3)) | r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))) & (k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1) | r1_tsep_1(X1,X2))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.71    inference(ennf_transformation,[],[f10])).
% 2.73/0.71  fof(f10,axiom,(
% 2.73/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((((~r1_tsep_1(X1,k2_tsep_1(X0,X2,X3)) & ~r1_tsep_1(X2,X3)) | (~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2))) => k2_tsep_1(X0,k2_tsep_1(X0,X1,X2),X3) = k2_tsep_1(X0,X1,k2_tsep_1(X0,X2,X3))) & (~r1_tsep_1(X1,X2) => k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1)))))))),
% 2.73/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tsep_1)).
% 2.73/0.71  fof(f378,plain,(
% 2.73/0.71    ~r1_tsep_1(sK3,sK1) | spl5_50),
% 2.73/0.71    inference(avatar_component_clause,[],[f376])).
% 2.73/0.71  fof(f143,plain,(
% 2.73/0.71    m1_pre_topc(sK1,sK0) | ~spl5_12),
% 2.73/0.71    inference(avatar_component_clause,[],[f141])).
% 2.73/0.71  fof(f123,plain,(
% 2.73/0.71    m1_pre_topc(sK3,sK0) | ~spl5_8),
% 2.73/0.71    inference(avatar_component_clause,[],[f121])).
% 2.73/0.71  fof(f148,plain,(
% 2.73/0.71    ~v2_struct_0(sK1) | spl5_13),
% 2.73/0.71    inference(avatar_component_clause,[],[f146])).
% 2.73/0.71  fof(f128,plain,(
% 2.73/0.71    ~v2_struct_0(sK3) | spl5_9),
% 2.73/0.71    inference(avatar_component_clause,[],[f126])).
% 2.73/0.71  fof(f153,plain,(
% 2.73/0.71    l1_pre_topc(sK0) | ~spl5_14),
% 2.73/0.71    inference(avatar_component_clause,[],[f151])).
% 2.73/0.71  fof(f158,plain,(
% 2.73/0.71    v2_pre_topc(sK0) | ~spl5_15),
% 2.73/0.71    inference(avatar_component_clause,[],[f156])).
% 2.73/0.72  fof(f163,plain,(
% 2.73/0.72    ~v2_struct_0(sK0) | spl5_16),
% 2.73/0.72    inference(avatar_component_clause,[],[f161])).
% 2.73/0.72  fof(f196,plain,(
% 2.73/0.72    sP4(sK0) | ~spl5_21),
% 2.73/0.72    inference(avatar_component_clause,[],[f194])).
% 2.73/0.72  fof(f4165,plain,(
% 2.73/0.72    ~spl5_48 | ~spl5_6 | spl5_7 | ~spl5_8 | spl5_9 | ~spl5_10 | spl5_11 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16),
% 2.73/0.72    inference(avatar_split_clause,[],[f3855,f161,f156,f151,f146,f141,f136,f131,f126,f121,f116,f110,f363])).
% 2.73/0.72  fof(f363,plain,(
% 2.73/0.72    spl5_48 <=> r1_tsep_1(sK1,sK3)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 2.73/0.72  fof(f110,plain,(
% 2.73/0.72    spl5_6 <=> m1_pre_topc(sK2,sK3)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.73/0.72  fof(f116,plain,(
% 2.73/0.72    spl5_7 <=> r1_tsep_1(sK1,sK2)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.73/0.72  fof(f131,plain,(
% 2.73/0.72    spl5_10 <=> m1_pre_topc(sK2,sK0)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.73/0.72  fof(f136,plain,(
% 2.73/0.72    spl5_11 <=> v2_struct_0(sK2)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.73/0.72  fof(f3855,plain,(
% 2.73/0.72    ~r1_tsep_1(sK1,sK3) | (~spl5_6 | spl5_7 | ~spl5_8 | spl5_9 | ~spl5_10 | spl5_11 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f163,f158,f153,f138,f148,f128,f133,f123,f143,f118,f112,f78])).
% 2.73/0.72  fof(f78,plain,(
% 2.73/0.72    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X3,X1) | ~r1_tsep_1(X3,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.72    inference(cnf_transformation,[],[f33])).
% 2.73/0.72  fof(f33,plain,(
% 2.73/0.72    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.72    inference(flattening,[],[f32])).
% 2.73/0.72  fof(f32,plain,(
% 2.73/0.72    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.72    inference(ennf_transformation,[],[f7])).
% 2.73/0.72  fof(f7,axiom,(
% 2.73/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 2.73/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).
% 2.73/0.72  fof(f112,plain,(
% 2.73/0.72    m1_pre_topc(sK2,sK3) | ~spl5_6),
% 2.73/0.72    inference(avatar_component_clause,[],[f110])).
% 2.73/0.72  fof(f118,plain,(
% 2.73/0.72    ~r1_tsep_1(sK1,sK2) | spl5_7),
% 2.73/0.72    inference(avatar_component_clause,[],[f116])).
% 2.73/0.72  fof(f133,plain,(
% 2.73/0.72    m1_pre_topc(sK2,sK0) | ~spl5_10),
% 2.73/0.72    inference(avatar_component_clause,[],[f131])).
% 2.73/0.72  fof(f138,plain,(
% 2.73/0.72    ~v2_struct_0(sK2) | spl5_11),
% 2.73/0.72    inference(avatar_component_clause,[],[f136])).
% 2.73/0.72  fof(f4164,plain,(
% 2.73/0.72    spl5_525 | ~spl5_3 | ~spl5_10 | spl5_11 | ~spl5_14 | ~spl5_15 | spl5_16 | spl5_30 | spl5_33 | ~spl5_40 | ~spl5_43 | ~spl5_553),
% 2.73/0.72    inference(avatar_split_clause,[],[f4151,f3896,f335,f320,f275,f260,f161,f156,f151,f136,f131,f96,f3673])).
% 2.73/0.72  fof(f3673,plain,(
% 2.73/0.72    spl5_525 <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_525])])).
% 2.73/0.72  fof(f96,plain,(
% 2.73/0.72    spl5_3 <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.73/0.72  fof(f260,plain,(
% 2.73/0.72    spl5_30 <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 2.73/0.72  fof(f275,plain,(
% 2.73/0.72    spl5_33 <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK3))),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 2.73/0.72  fof(f320,plain,(
% 2.73/0.72    spl5_40 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 2.73/0.72  fof(f335,plain,(
% 2.73/0.72    spl5_43 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 2.73/0.72  fof(f3896,plain,(
% 2.73/0.72    spl5_553 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_553])])).
% 2.73/0.72  fof(f4151,plain,(
% 2.73/0.72    r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2) | (~spl5_3 | ~spl5_10 | spl5_11 | ~spl5_14 | ~spl5_15 | spl5_16 | spl5_30 | spl5_33 | ~spl5_40 | ~spl5_43 | ~spl5_553)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f163,f158,f153,f138,f133,f262,f277,f322,f337,f98,f3898,f75])).
% 2.73/0.72  fof(f75,plain,(
% 2.73/0.72    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X1,X3) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.72    inference(cnf_transformation,[],[f33])).
% 2.73/0.72  fof(f3898,plain,(
% 2.73/0.72    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) | ~spl5_553),
% 2.73/0.72    inference(avatar_component_clause,[],[f3896])).
% 2.73/0.72  fof(f98,plain,(
% 2.73/0.72    r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) | ~spl5_3),
% 2.73/0.72    inference(avatar_component_clause,[],[f96])).
% 2.73/0.72  fof(f337,plain,(
% 2.73/0.72    m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) | ~spl5_43),
% 2.73/0.72    inference(avatar_component_clause,[],[f335])).
% 2.73/0.72  fof(f322,plain,(
% 2.73/0.72    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | ~spl5_40),
% 2.73/0.72    inference(avatar_component_clause,[],[f320])).
% 2.73/0.72  fof(f277,plain,(
% 2.73/0.72    ~v2_struct_0(k2_tsep_1(sK0,sK1,sK3)) | spl5_33),
% 2.73/0.72    inference(avatar_component_clause,[],[f275])).
% 2.73/0.72  fof(f262,plain,(
% 2.73/0.72    ~v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | spl5_30),
% 2.73/0.72    inference(avatar_component_clause,[],[f260])).
% 2.73/0.72  fof(f3900,plain,(
% 2.73/0.72    spl5_553 | ~spl5_6 | spl5_7 | ~spl5_8 | spl5_9 | ~spl5_10 | spl5_11 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_52),
% 2.73/0.72    inference(avatar_split_clause,[],[f3852,f387,f161,f156,f151,f146,f141,f136,f131,f126,f121,f116,f110,f3896])).
% 2.73/0.72  fof(f387,plain,(
% 2.73/0.72    spl5_52 <=> m1_pre_topc(sK1,sK1)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 2.73/0.72  fof(f3852,plain,(
% 2.73/0.72    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) | (~spl5_6 | spl5_7 | ~spl5_8 | spl5_9 | ~spl5_10 | spl5_11 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_52)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f163,f158,f153,f148,f148,f138,f128,f143,f133,f143,f123,f389,f118,f112,f63])).
% 2.73/0.72  fof(f63,plain,(
% 2.73/0.72    ( ! [X4,X2,X0,X3,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X4) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.72    inference(cnf_transformation,[],[f23])).
% 2.73/0.72  fof(f23,plain,(
% 2.73/0.72    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X4) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.72    inference(flattening,[],[f22])).
% 2.73/0.72  fof(f22,plain,(
% 2.73/0.72    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X4) | ~m1_pre_topc(X1,X3))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.72    inference(ennf_transformation,[],[f9])).
% 2.73/0.72  fof(f9,axiom,(
% 2.73/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2))))))))),
% 2.73/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tmap_1)).
% 2.73/0.72  fof(f389,plain,(
% 2.73/0.72    m1_pre_topc(sK1,sK1) | ~spl5_52),
% 2.73/0.72    inference(avatar_component_clause,[],[f387])).
% 2.73/0.72  fof(f3828,plain,(
% 2.73/0.72    spl5_512 | ~spl5_2 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16 | spl5_30 | spl5_31 | ~spl5_40 | ~spl5_41 | ~spl5_160),
% 2.73/0.72    inference(avatar_split_clause,[],[f3815,f1078,f325,f320,f265,f260,f161,f156,f151,f146,f141,f92,f3576])).
% 2.73/0.72  fof(f3576,plain,(
% 2.73/0.72    spl5_512 <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_512])])).
% 2.73/0.72  fof(f92,plain,(
% 2.73/0.72    spl5_2 <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.73/0.72  fof(f265,plain,(
% 2.73/0.72    spl5_31 <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK3))),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 2.73/0.72  fof(f325,plain,(
% 2.73/0.72    spl5_41 <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 2.73/0.72  fof(f1078,plain,(
% 2.73/0.72    spl5_160 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK2,sK3))),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_160])])).
% 2.73/0.72  fof(f3815,plain,(
% 2.73/0.72    r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1) | (~spl5_2 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16 | spl5_30 | spl5_31 | ~spl5_40 | ~spl5_41 | ~spl5_160)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f163,f158,f153,f148,f143,f262,f267,f322,f327,f94,f1080,f75])).
% 2.73/0.72  fof(f1080,plain,(
% 2.73/0.72    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK2,sK3)) | ~spl5_160),
% 2.73/0.72    inference(avatar_component_clause,[],[f1078])).
% 2.73/0.72  fof(f94,plain,(
% 2.73/0.72    r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | ~spl5_2),
% 2.73/0.72    inference(avatar_component_clause,[],[f92])).
% 2.73/0.72  fof(f327,plain,(
% 2.73/0.72    m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0) | ~spl5_41),
% 2.73/0.72    inference(avatar_component_clause,[],[f325])).
% 2.73/0.72  fof(f267,plain,(
% 2.73/0.72    ~v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) | spl5_31),
% 2.73/0.72    inference(avatar_component_clause,[],[f265])).
% 2.73/0.72  fof(f3677,plain,(
% 2.73/0.72    ~spl5_525 | ~spl5_10 | spl5_11 | ~spl5_14 | ~spl5_15 | spl5_16 | spl5_30 | ~spl5_40 | ~spl5_63),
% 2.73/0.72    inference(avatar_split_clause,[],[f3637,f453,f320,f260,f161,f156,f151,f136,f131,f3673])).
% 2.73/0.72  fof(f453,plain,(
% 2.73/0.72    spl5_63 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 2.73/0.72  fof(f3637,plain,(
% 2.73/0.72    ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2) | (~spl5_10 | spl5_11 | ~spl5_14 | ~spl5_15 | spl5_16 | spl5_30 | ~spl5_40 | ~spl5_63)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f163,f158,f153,f138,f133,f262,f322,f455,f79])).
% 2.73/0.72  fof(f79,plain,(
% 2.73/0.72    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~r1_tsep_1(X1,X2) | v2_struct_0(X0)) )),
% 2.73/0.72    inference(cnf_transformation,[],[f35])).
% 2.73/0.72  fof(f35,plain,(
% 2.73/0.72    ! [X0] : (! [X1] : (! [X2] : ((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.72    inference(flattening,[],[f34])).
% 2.73/0.72  fof(f34,plain,(
% 2.73/0.72    ! [X0] : (! [X1] : (! [X2] : (((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.72    inference(ennf_transformation,[],[f5])).
% 2.73/0.72  fof(f5,axiom,(
% 2.73/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 2.73/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).
% 2.73/0.72  fof(f455,plain,(
% 2.73/0.72    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) | ~spl5_63),
% 2.73/0.72    inference(avatar_component_clause,[],[f453])).
% 2.73/0.72  fof(f3624,plain,(
% 2.73/0.72    k2_tsep_1(sK0,sK2,sK3) != k2_tsep_1(sK0,sK3,sK2) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | ~r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)),
% 2.73/0.72    introduced(theory_tautology_sat_conflict,[])).
% 2.73/0.72  fof(f3581,plain,(
% 2.73/0.72    ~spl5_512 | spl5_13 | ~spl5_20 | ~spl5_26 | spl5_30 | ~spl5_52 | ~spl5_62),
% 2.73/0.72    inference(avatar_split_clause,[],[f3539,f447,f387,f260,f228,f185,f146,f3576])).
% 2.73/0.72  fof(f185,plain,(
% 2.73/0.72    spl5_20 <=> l1_pre_topc(sK1)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 2.73/0.72  fof(f228,plain,(
% 2.73/0.72    spl5_26 <=> v2_pre_topc(sK1)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 2.73/0.72  fof(f447,plain,(
% 2.73/0.72    spl5_62 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 2.73/0.72  fof(f3539,plain,(
% 2.73/0.72    ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1) | (spl5_13 | ~spl5_20 | ~spl5_26 | spl5_30 | ~spl5_52 | ~spl5_62)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f148,f230,f187,f148,f389,f262,f449,f449,f79])).
% 2.73/0.72  fof(f449,plain,(
% 2.73/0.72    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) | ~spl5_62),
% 2.73/0.72    inference(avatar_component_clause,[],[f447])).
% 2.73/0.72  fof(f187,plain,(
% 2.73/0.72    l1_pre_topc(sK1) | ~spl5_20),
% 2.73/0.72    inference(avatar_component_clause,[],[f185])).
% 2.73/0.72  fof(f230,plain,(
% 2.73/0.72    v2_pre_topc(sK1) | ~spl5_26),
% 2.73/0.72    inference(avatar_component_clause,[],[f228])).
% 2.73/0.72  fof(f2952,plain,(
% 2.73/0.72    spl5_3 | ~spl5_4 | ~spl5_116),
% 2.73/0.72    inference(avatar_split_clause,[],[f2951,f807,f100,f96])).
% 2.73/0.72  fof(f100,plain,(
% 2.73/0.72    spl5_4 <=> r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.73/0.72  fof(f2951,plain,(
% 2.73/0.72    r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) | (~spl5_4 | ~spl5_116)),
% 2.73/0.72    inference(forward_demodulation,[],[f102,f809])).
% 2.73/0.72  fof(f809,plain,(
% 2.73/0.72    k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3) | ~spl5_116),
% 2.73/0.72    inference(avatar_component_clause,[],[f807])).
% 2.73/0.72  fof(f102,plain,(
% 2.73/0.72    r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | ~spl5_4),
% 2.73/0.72    inference(avatar_component_clause,[],[f100])).
% 2.73/0.72  fof(f1081,plain,(
% 2.73/0.72    spl5_160 | ~spl5_78 | ~spl5_146),
% 2.73/0.72    inference(avatar_split_clause,[],[f1071,f1008,f532,f1078])).
% 2.73/0.72  fof(f532,plain,(
% 2.73/0.72    spl5_78 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).
% 2.73/0.72  fof(f1008,plain,(
% 2.73/0.72    spl5_146 <=> k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).
% 2.73/0.72  fof(f1071,plain,(
% 2.73/0.72    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK2,sK3)) | (~spl5_78 | ~spl5_146)),
% 2.73/0.72    inference(backward_demodulation,[],[f534,f1010])).
% 2.73/0.72  fof(f1010,plain,(
% 2.73/0.72    k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2) | ~spl5_146),
% 2.73/0.72    inference(avatar_component_clause,[],[f1008])).
% 2.73/0.72  fof(f534,plain,(
% 2.73/0.72    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) | ~spl5_78),
% 2.73/0.72    inference(avatar_component_clause,[],[f532])).
% 2.73/0.72  fof(f1011,plain,(
% 2.73/0.72    spl5_146 | ~spl5_8 | spl5_9 | ~spl5_10 | spl5_11 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_21 | spl5_64),
% 2.73/0.72    inference(avatar_split_clause,[],[f999,f460,f194,f161,f156,f151,f136,f131,f126,f121,f1008])).
% 2.73/0.72  fof(f460,plain,(
% 2.73/0.72    spl5_64 <=> r1_tsep_1(sK3,sK2)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).
% 2.73/0.72  fof(f999,plain,(
% 2.73/0.72    k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2) | (~spl5_8 | spl5_9 | ~spl5_10 | spl5_11 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_21 | spl5_64)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f196,f163,f158,f153,f128,f138,f123,f133,f462,f86])).
% 2.73/0.72  fof(f462,plain,(
% 2.73/0.72    ~r1_tsep_1(sK3,sK2) | spl5_64),
% 2.73/0.72    inference(avatar_component_clause,[],[f460])).
% 2.73/0.72  fof(f810,plain,(
% 2.73/0.72    spl5_116 | ~spl5_8 | spl5_9 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_21 | spl5_48),
% 2.73/0.72    inference(avatar_split_clause,[],[f798,f363,f194,f161,f156,f151,f146,f141,f126,f121,f807])).
% 2.73/0.72  fof(f798,plain,(
% 2.73/0.72    k2_tsep_1(sK0,sK3,sK1) = k2_tsep_1(sK0,sK1,sK3) | (~spl5_8 | spl5_9 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_21 | spl5_48)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f196,f163,f158,f153,f148,f128,f143,f123,f365,f86])).
% 2.73/0.72  fof(f365,plain,(
% 2.73/0.72    ~r1_tsep_1(sK1,sK3) | spl5_48),
% 2.73/0.72    inference(avatar_component_clause,[],[f363])).
% 2.73/0.72  fof(f535,plain,(
% 2.73/0.72    spl5_78 | ~spl5_5 | spl5_7 | ~spl5_8 | spl5_9 | ~spl5_10 | spl5_11 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16),
% 2.73/0.72    inference(avatar_split_clause,[],[f530,f161,f156,f151,f146,f141,f136,f131,f126,f121,f116,f105,f532])).
% 2.73/0.72  fof(f105,plain,(
% 2.73/0.72    spl5_5 <=> m1_pre_topc(sK1,sK3)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.73/0.72  fof(f530,plain,(
% 2.73/0.72    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) | (~spl5_5 | spl5_7 | ~spl5_8 | spl5_9 | ~spl5_10 | spl5_11 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f163,f158,f153,f148,f128,f138,f143,f133,f123,f118,f107,f64])).
% 2.73/0.72  fof(f64,plain,(
% 2.73/0.72    ( ! [X2,X0,X3,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) | ~m1_pre_topc(X1,X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.72    inference(cnf_transformation,[],[f25])).
% 2.73/0.72  fof(f25,plain,(
% 2.73/0.72    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) | ~m1_pre_topc(X2,X3)) & (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) | ~m1_pre_topc(X1,X3))) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.72    inference(flattening,[],[f24])).
% 2.73/0.72  fof(f24,plain,(
% 2.73/0.72    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) | ~m1_pre_topc(X2,X3)) & (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) | ~m1_pre_topc(X1,X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.72    inference(ennf_transformation,[],[f14])).
% 2.73/0.72  fof(f14,axiom,(
% 2.73/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))) & (m1_pre_topc(X1,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)))))))))),
% 2.73/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tmap_1)).
% 2.73/0.72  fof(f107,plain,(
% 2.73/0.72    m1_pre_topc(sK1,sK3) | ~spl5_5),
% 2.73/0.72    inference(avatar_component_clause,[],[f105])).
% 2.73/0.72  fof(f463,plain,(
% 2.73/0.72    ~spl5_64 | ~spl5_5 | spl5_7 | ~spl5_8 | spl5_9 | ~spl5_10 | spl5_11 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16),
% 2.73/0.72    inference(avatar_split_clause,[],[f457,f161,f156,f151,f146,f141,f136,f131,f126,f121,f116,f105,f460])).
% 2.73/0.72  fof(f457,plain,(
% 2.73/0.72    ~r1_tsep_1(sK3,sK2) | (~spl5_5 | spl5_7 | ~spl5_8 | spl5_9 | ~spl5_10 | spl5_11 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f163,f158,f153,f148,f138,f128,f143,f123,f133,f107,f118,f75])).
% 2.73/0.72  fof(f456,plain,(
% 2.73/0.72    spl5_63 | spl5_7 | ~spl5_10 | spl5_11 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16),
% 2.73/0.72    inference(avatar_split_clause,[],[f451,f161,f156,f151,f146,f141,f136,f131,f116,f453])).
% 2.73/0.72  fof(f451,plain,(
% 2.73/0.72    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) | (spl5_7 | ~spl5_10 | spl5_11 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f163,f158,f153,f148,f138,f143,f133,f118,f74])).
% 2.73/0.72  fof(f74,plain,(
% 2.73/0.72    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.72    inference(cnf_transformation,[],[f31])).
% 2.73/0.72  fof(f31,plain,(
% 2.73/0.72    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.72    inference(flattening,[],[f30])).
% 2.73/0.72  fof(f30,plain,(
% 2.73/0.72    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.72    inference(ennf_transformation,[],[f12])).
% 2.73/0.72  fof(f12,axiom,(
% 2.73/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1))))))),
% 2.73/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tsep_1)).
% 2.73/0.72  fof(f450,plain,(
% 2.73/0.72    spl5_62 | spl5_7 | ~spl5_10 | spl5_11 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16),
% 2.73/0.72    inference(avatar_split_clause,[],[f445,f161,f156,f151,f146,f141,f136,f131,f116,f447])).
% 2.73/0.72  fof(f445,plain,(
% 2.73/0.72    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) | (spl5_7 | ~spl5_10 | spl5_11 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f163,f158,f153,f148,f138,f143,f133,f118,f73])).
% 2.73/0.72  fof(f73,plain,(
% 2.73/0.72    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.72    inference(cnf_transformation,[],[f31])).
% 2.73/0.72  fof(f390,plain,(
% 2.73/0.72    spl5_52 | ~spl5_20),
% 2.73/0.72    inference(avatar_split_clause,[],[f385,f185,f387])).
% 2.73/0.72  fof(f385,plain,(
% 2.73/0.72    m1_pre_topc(sK1,sK1) | ~spl5_20),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f187,f84])).
% 2.73/0.72  fof(f84,plain,(
% 2.73/0.72    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.73/0.72    inference(cnf_transformation,[],[f41])).
% 2.73/0.72  fof(f41,plain,(
% 2.73/0.72    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.73/0.72    inference(ennf_transformation,[],[f11])).
% 2.73/0.72  fof(f11,axiom,(
% 2.73/0.72    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.73/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.73/0.72  fof(f379,plain,(
% 2.73/0.72    ~spl5_50 | ~spl5_5 | ~spl5_8 | spl5_9 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16),
% 2.73/0.72    inference(avatar_split_clause,[],[f372,f161,f156,f151,f146,f141,f126,f121,f105,f376])).
% 2.73/0.72  fof(f372,plain,(
% 2.73/0.72    ~r1_tsep_1(sK3,sK1) | (~spl5_5 | ~spl5_8 | spl5_9 | ~spl5_12 | spl5_13 | ~spl5_14 | ~spl5_15 | spl5_16)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f163,f128,f153,f148,f143,f107,f123,f158,f80])).
% 2.73/0.72  fof(f80,plain,(
% 2.73/0.72    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~r1_tsep_1(X2,X1) | v2_struct_0(X0)) )),
% 2.73/0.72    inference(cnf_transformation,[],[f35])).
% 2.73/0.72  fof(f338,plain,(
% 2.73/0.72    spl5_43 | ~spl5_8 | spl5_9 | ~spl5_12 | spl5_13 | ~spl5_14 | spl5_16),
% 2.73/0.72    inference(avatar_split_clause,[],[f303,f161,f151,f146,f141,f126,f121,f335])).
% 2.73/0.72  fof(f303,plain,(
% 2.73/0.72    m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) | (~spl5_8 | spl5_9 | ~spl5_12 | spl5_13 | ~spl5_14 | spl5_16)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f163,f153,f148,f143,f128,f123,f62])).
% 2.73/0.72  fof(f62,plain,(
% 2.73/0.72    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.72    inference(cnf_transformation,[],[f21])).
% 2.73/0.72  fof(f21,plain,(
% 2.73/0.72    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.72    inference(flattening,[],[f20])).
% 2.73/0.72  fof(f20,plain,(
% 2.73/0.72    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.72    inference(ennf_transformation,[],[f17])).
% 2.73/0.72  fof(f17,plain,(
% 2.73/0.72    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 2.73/0.72    inference(pure_predicate_removal,[],[f4])).
% 2.73/0.72  fof(f4,axiom,(
% 2.73/0.72    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 2.73/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 2.73/0.72  fof(f328,plain,(
% 2.73/0.72    spl5_41 | ~spl5_8 | spl5_9 | ~spl5_10 | spl5_11 | ~spl5_14 | spl5_16),
% 2.73/0.72    inference(avatar_split_clause,[],[f305,f161,f151,f136,f131,f126,f121,f325])).
% 2.73/0.72  fof(f305,plain,(
% 2.73/0.72    m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0) | (~spl5_8 | spl5_9 | ~spl5_10 | spl5_11 | ~spl5_14 | spl5_16)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f163,f153,f138,f133,f128,f123,f62])).
% 2.73/0.72  fof(f323,plain,(
% 2.73/0.72    spl5_40 | ~spl5_10 | spl5_11 | ~spl5_12 | spl5_13 | ~spl5_14 | spl5_16),
% 2.73/0.72    inference(avatar_split_clause,[],[f306,f161,f151,f146,f141,f136,f131,f320])).
% 2.73/0.72  fof(f306,plain,(
% 2.73/0.72    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | (~spl5_10 | spl5_11 | ~spl5_12 | spl5_13 | ~spl5_14 | spl5_16)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f163,f153,f148,f143,f138,f133,f62])).
% 2.73/0.72  fof(f278,plain,(
% 2.73/0.72    ~spl5_33 | ~spl5_8 | spl5_9 | ~spl5_12 | spl5_13 | ~spl5_14 | spl5_16),
% 2.73/0.72    inference(avatar_split_clause,[],[f243,f161,f151,f146,f141,f126,f121,f275])).
% 2.73/0.72  fof(f243,plain,(
% 2.73/0.72    ~v2_struct_0(k2_tsep_1(sK0,sK1,sK3)) | (~spl5_8 | spl5_9 | ~spl5_12 | spl5_13 | ~spl5_14 | spl5_16)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f163,f153,f148,f143,f128,f123,f61])).
% 2.73/0.72  fof(f61,plain,(
% 2.73/0.72    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.72    inference(cnf_transformation,[],[f21])).
% 2.73/0.72  fof(f268,plain,(
% 2.73/0.72    ~spl5_31 | ~spl5_8 | spl5_9 | ~spl5_10 | spl5_11 | ~spl5_14 | spl5_16),
% 2.73/0.72    inference(avatar_split_clause,[],[f245,f161,f151,f136,f131,f126,f121,f265])).
% 2.73/0.72  fof(f245,plain,(
% 2.73/0.72    ~v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) | (~spl5_8 | spl5_9 | ~spl5_10 | spl5_11 | ~spl5_14 | spl5_16)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f163,f153,f138,f133,f128,f123,f61])).
% 2.73/0.72  fof(f263,plain,(
% 2.73/0.72    ~spl5_30 | ~spl5_10 | spl5_11 | ~spl5_12 | spl5_13 | ~spl5_14 | spl5_16),
% 2.73/0.72    inference(avatar_split_clause,[],[f246,f161,f151,f146,f141,f136,f131,f260])).
% 2.73/0.72  fof(f246,plain,(
% 2.73/0.72    ~v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | (~spl5_10 | spl5_11 | ~spl5_12 | spl5_13 | ~spl5_14 | spl5_16)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f163,f153,f148,f143,f138,f133,f61])).
% 2.73/0.72  fof(f231,plain,(
% 2.73/0.72    spl5_26 | ~spl5_12 | ~spl5_14 | ~spl5_15),
% 2.73/0.72    inference(avatar_split_clause,[],[f214,f156,f151,f141,f228])).
% 2.73/0.72  fof(f214,plain,(
% 2.73/0.72    v2_pre_topc(sK1) | (~spl5_12 | ~spl5_14 | ~spl5_15)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f158,f153,f143,f81])).
% 2.73/0.72  fof(f81,plain,(
% 2.73/0.72    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.73/0.72    inference(cnf_transformation,[],[f37])).
% 2.73/0.72  fof(f37,plain,(
% 2.73/0.72    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.73/0.72    inference(flattening,[],[f36])).
% 2.73/0.72  fof(f36,plain,(
% 2.73/0.72    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.73/0.72    inference(ennf_transformation,[],[f1])).
% 2.73/0.72  fof(f1,axiom,(
% 2.73/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.73/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 2.73/0.72  fof(f199,plain,(
% 2.73/0.72    spl5_21 | ~spl5_12 | spl5_13),
% 2.73/0.72    inference(avatar_split_clause,[],[f190,f146,f141,f194])).
% 2.73/0.72  fof(f190,plain,(
% 2.73/0.72    sP4(sK0) | (~spl5_12 | spl5_13)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f143,f148,f85])).
% 2.73/0.72  fof(f188,plain,(
% 2.73/0.72    spl5_20 | ~spl5_12 | ~spl5_14),
% 2.73/0.72    inference(avatar_split_clause,[],[f171,f151,f141,f185])).
% 2.73/0.72  fof(f171,plain,(
% 2.73/0.72    l1_pre_topc(sK1) | (~spl5_12 | ~spl5_14)),
% 2.73/0.72    inference(unit_resulting_resolution,[],[f153,f143,f83])).
% 2.73/0.72  fof(f83,plain,(
% 2.73/0.72    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.73/0.72    inference(cnf_transformation,[],[f40])).
% 2.73/0.72  fof(f40,plain,(
% 2.73/0.72    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.73/0.72    inference(ennf_transformation,[],[f2])).
% 2.73/0.72  fof(f2,axiom,(
% 2.73/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.73/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.73/0.72  fof(f164,plain,(
% 2.73/0.72    ~spl5_16),
% 2.73/0.72    inference(avatar_split_clause,[],[f47,f161])).
% 2.73/0.72  fof(f47,plain,(
% 2.73/0.72    ~v2_struct_0(sK0)),
% 2.73/0.72    inference(cnf_transformation,[],[f46])).
% 2.73/0.72  fof(f46,plain,(
% 2.73/0.72    ((((((r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)) & m1_pre_topc(sK2,sK3)) | ((r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)) & m1_pre_topc(sK1,sK3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.73/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f45,f44,f43,f42])).
% 2.73/0.72  fof(f42,plain,(
% 2.73/0.72    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(sK0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(sK0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(sK0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(sK0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.73/0.72    introduced(choice_axiom,[])).
% 2.73/0.72  fof(f43,plain,(
% 2.73/0.72    ? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(sK0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(sK0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(sK0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(sK0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(sK0,X3,sK1),X2) | r1_tsep_1(k2_tsep_1(sK0,sK1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(sK0,X2,X3),sK1) | r1_tsep_1(k2_tsep_1(sK0,X3,X2),sK1)) & m1_pre_topc(sK1,X3))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 2.73/0.72    introduced(choice_axiom,[])).
% 2.73/0.72  fof(f44,plain,(
% 2.73/0.72    ? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(sK0,X3,sK1),X2) | r1_tsep_1(k2_tsep_1(sK0,sK1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(sK0,X2,X3),sK1) | r1_tsep_1(k2_tsep_1(sK0,X3,X2),sK1)) & m1_pre_topc(sK1,X3))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : ((((r1_tsep_1(k2_tsep_1(sK0,X3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,X3),sK2)) & m1_pre_topc(sK2,X3)) | ((r1_tsep_1(k2_tsep_1(sK0,sK2,X3),sK1) | r1_tsep_1(k2_tsep_1(sK0,X3,sK2),sK1)) & m1_pre_topc(sK1,X3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 2.73/0.72    introduced(choice_axiom,[])).
% 2.73/0.72  fof(f45,plain,(
% 2.73/0.72    ? [X3] : ((((r1_tsep_1(k2_tsep_1(sK0,X3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,X3),sK2)) & m1_pre_topc(sK2,X3)) | ((r1_tsep_1(k2_tsep_1(sK0,sK2,X3),sK1) | r1_tsep_1(k2_tsep_1(sK0,X3,sK2),sK1)) & m1_pre_topc(sK1,X3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => ((((r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)) & m1_pre_topc(sK2,sK3)) | ((r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)) & m1_pre_topc(sK1,sK3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 2.73/0.72    introduced(choice_axiom,[])).
% 2.73/0.72  fof(f19,plain,(
% 2.73/0.72    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.73/0.72    inference(flattening,[],[f18])).
% 2.73/0.72  fof(f18,plain,(
% 2.73/0.72    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((((r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.73/0.72    inference(ennf_transformation,[],[f16])).
% 2.73/0.72  fof(f16,negated_conjecture,(
% 2.73/0.72    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => (~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2))) & (m1_pre_topc(X1,X3) => (~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)))))))))),
% 2.73/0.72    inference(negated_conjecture,[],[f15])).
% 2.73/0.72  fof(f15,conjecture,(
% 2.73/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => (~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2))) & (m1_pre_topc(X1,X3) => (~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)))))))))),
% 2.73/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tmap_1)).
% 2.73/0.72  fof(f159,plain,(
% 2.73/0.72    spl5_15),
% 2.73/0.72    inference(avatar_split_clause,[],[f48,f156])).
% 2.73/0.72  fof(f48,plain,(
% 2.73/0.72    v2_pre_topc(sK0)),
% 2.73/0.72    inference(cnf_transformation,[],[f46])).
% 2.73/0.72  fof(f154,plain,(
% 2.73/0.72    spl5_14),
% 2.73/0.72    inference(avatar_split_clause,[],[f49,f151])).
% 2.73/0.72  fof(f49,plain,(
% 2.73/0.72    l1_pre_topc(sK0)),
% 2.73/0.72    inference(cnf_transformation,[],[f46])).
% 2.73/0.72  fof(f149,plain,(
% 2.73/0.72    ~spl5_13),
% 2.73/0.72    inference(avatar_split_clause,[],[f50,f146])).
% 2.73/0.72  fof(f50,plain,(
% 2.73/0.72    ~v2_struct_0(sK1)),
% 2.73/0.72    inference(cnf_transformation,[],[f46])).
% 2.73/0.72  fof(f144,plain,(
% 2.73/0.72    spl5_12),
% 2.73/0.72    inference(avatar_split_clause,[],[f51,f141])).
% 2.73/0.72  fof(f51,plain,(
% 2.73/0.72    m1_pre_topc(sK1,sK0)),
% 2.73/0.72    inference(cnf_transformation,[],[f46])).
% 2.73/0.72  fof(f139,plain,(
% 2.73/0.72    ~spl5_11),
% 2.73/0.72    inference(avatar_split_clause,[],[f52,f136])).
% 2.73/0.72  fof(f52,plain,(
% 2.73/0.72    ~v2_struct_0(sK2)),
% 2.73/0.72    inference(cnf_transformation,[],[f46])).
% 2.73/0.72  fof(f134,plain,(
% 2.73/0.72    spl5_10),
% 2.73/0.72    inference(avatar_split_clause,[],[f53,f131])).
% 2.73/0.72  fof(f53,plain,(
% 2.73/0.72    m1_pre_topc(sK2,sK0)),
% 2.73/0.72    inference(cnf_transformation,[],[f46])).
% 2.73/0.72  fof(f129,plain,(
% 2.73/0.72    ~spl5_9),
% 2.73/0.72    inference(avatar_split_clause,[],[f54,f126])).
% 2.73/0.72  fof(f54,plain,(
% 2.73/0.72    ~v2_struct_0(sK3)),
% 2.73/0.72    inference(cnf_transformation,[],[f46])).
% 2.73/0.72  fof(f124,plain,(
% 2.73/0.72    spl5_8),
% 2.73/0.72    inference(avatar_split_clause,[],[f55,f121])).
% 2.73/0.72  fof(f55,plain,(
% 2.73/0.72    m1_pre_topc(sK3,sK0)),
% 2.73/0.72    inference(cnf_transformation,[],[f46])).
% 2.73/0.72  fof(f119,plain,(
% 2.73/0.72    ~spl5_7),
% 2.73/0.72    inference(avatar_split_clause,[],[f56,f116])).
% 2.73/0.72  fof(f56,plain,(
% 2.73/0.72    ~r1_tsep_1(sK1,sK2)),
% 2.73/0.72    inference(cnf_transformation,[],[f46])).
% 2.73/0.72  fof(f114,plain,(
% 2.73/0.72    spl5_5 | spl5_6),
% 2.73/0.72    inference(avatar_split_clause,[],[f57,f110,f105])).
% 2.73/0.72  fof(f57,plain,(
% 2.73/0.72    m1_pre_topc(sK2,sK3) | m1_pre_topc(sK1,sK3)),
% 2.73/0.72    inference(cnf_transformation,[],[f46])).
% 2.73/0.72  fof(f113,plain,(
% 2.73/0.72    spl5_1 | spl5_2 | spl5_6),
% 2.73/0.72    inference(avatar_split_clause,[],[f58,f110,f92,f88])).
% 2.73/0.72  fof(f88,plain,(
% 2.73/0.72    spl5_1 <=> r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)),
% 2.73/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.73/0.72  fof(f58,plain,(
% 2.73/0.72    m1_pre_topc(sK2,sK3) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)),
% 2.73/0.72    inference(cnf_transformation,[],[f46])).
% 2.73/0.72  fof(f108,plain,(
% 2.73/0.72    spl5_5 | spl5_3 | spl5_4),
% 2.73/0.72    inference(avatar_split_clause,[],[f59,f100,f96,f105])).
% 2.73/0.72  fof(f59,plain,(
% 2.73/0.72    r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) | m1_pre_topc(sK1,sK3)),
% 2.73/0.72    inference(cnf_transformation,[],[f46])).
% 2.73/0.72  fof(f103,plain,(
% 2.73/0.72    spl5_1 | spl5_2 | spl5_3 | spl5_4),
% 2.73/0.72    inference(avatar_split_clause,[],[f60,f100,f96,f92,f88])).
% 2.73/0.72  fof(f60,plain,(
% 2.73/0.72    r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)),
% 2.73/0.72    inference(cnf_transformation,[],[f46])).
% 2.73/0.72  % SZS output end Proof for theBenchmark
% 2.73/0.72  % (10383)------------------------------
% 2.73/0.72  % (10383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.73/0.72  % (10383)Termination reason: Refutation
% 2.73/0.72  
% 2.73/0.72  % (10383)Memory used [KB]: 15351
% 2.73/0.72  % (10383)Time elapsed: 0.276 s
% 2.73/0.72  % (10383)------------------------------
% 2.73/0.72  % (10383)------------------------------
% 2.73/0.73  % (10376)Success in time 0.364 s
%------------------------------------------------------------------------------
