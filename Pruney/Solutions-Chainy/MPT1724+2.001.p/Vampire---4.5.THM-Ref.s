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
% DateTime   : Thu Dec  3 13:18:07 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 429 expanded)
%              Number of leaves         :   33 ( 234 expanded)
%              Depth                    :    7
%              Number of atoms          :  720 (2980 expanded)
%              Number of equality atoms :   94 ( 445 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (13242)Termination reason: Refutation not found, incomplete strategy

% (13242)Memory used [KB]: 10618
% (13242)Time elapsed: 0.104 s
% (13242)------------------------------
% (13242)------------------------------
fof(f1203,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f79,f84,f89,f94,f99,f104,f109,f114,f119,f124,f129,f137,f154,f295,f422,f516,f526,f534,f916,f918,f1195,f1199,f1202])).

fof(f1202,plain,
    ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) != k2_tsep_1(sK2,sK3,sK4)
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK3,sK4)
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1199,plain,
    ( spl6_15
    | ~ spl6_4
    | spl6_79
    | ~ spl6_60
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f1198,f531,f419,f523,f76,f134])).

fof(f134,plain,
    ( spl6_15
  <=> r1_tsep_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f76,plain,
    ( spl6_4
  <=> r1_tsep_1(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f523,plain,
    ( spl6_79
  <=> k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) = k2_tsep_1(sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f419,plain,
    ( spl6_60
  <=> sP1(sK3,sK4,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f531,plain,
    ( spl6_80
  <=> k2_tsep_1(sK2,sK3,sK4) = k2_tsep_1(sK2,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f1198,plain,
    ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) = k2_tsep_1(sK2,sK3,sK4)
    | ~ r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK3,sK4)
    | ~ spl6_60
    | ~ spl6_80 ),
    inference(forward_demodulation,[],[f1179,f533])).

fof(f533,plain,
    ( k2_tsep_1(sK2,sK3,sK4) = k2_tsep_1(sK2,sK4,sK3)
    | ~ spl6_80 ),
    inference(avatar_component_clause,[],[f531])).

fof(f1179,plain,
    ( ~ r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK3,sK4)
    | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) = k2_tsep_1(sK2,sK4,sK3)
    | ~ spl6_60 ),
    inference(resolution,[],[f421,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ r1_tsep_1(X3,X1)
      | r1_tsep_1(X0,X1)
      | k2_tsep_1(X2,X1,k1_tsep_1(X2,X0,X3)) = k2_tsep_1(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k2_tsep_1(X2,X1,k1_tsep_1(X2,X0,X3)) = k2_tsep_1(X2,X1,X0)
        & k2_tsep_1(X2,k1_tsep_1(X2,X0,X3),X1) = k2_tsep_1(X2,X0,X1) )
      | ( ~ r1_tsep_1(X1,X3)
        & ~ r1_tsep_1(X3,X1) )
      | ( r1_tsep_1(X1,X0)
        & r1_tsep_1(X0,X1) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X1,X2,X0,X3] :
      ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X1)
        & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X1,X2) )
      | ( ~ r1_tsep_1(X2,X3)
        & ~ r1_tsep_1(X3,X2) )
      | ( r1_tsep_1(X2,X1)
        & r1_tsep_1(X1,X2) )
      | ~ sP1(X1,X2,X0,X3) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X1,X2,X0,X3] :
      ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X1)
        & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X1,X2) )
      | ( ~ r1_tsep_1(X2,X3)
        & ~ r1_tsep_1(X3,X2) )
      | ( r1_tsep_1(X2,X1)
        & r1_tsep_1(X1,X2) )
      | ~ sP1(X1,X2,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f421,plain,
    ( sP1(sK3,sK4,sK2,sK5)
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f419])).

fof(f1195,plain,
    ( spl6_15
    | ~ spl6_3
    | spl6_79
    | ~ spl6_60
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f1194,f531,f419,f523,f72,f134])).

fof(f72,plain,
    ( spl6_3
  <=> r1_tsep_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1194,plain,
    ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) = k2_tsep_1(sK2,sK3,sK4)
    | ~ r1_tsep_1(sK4,sK5)
    | r1_tsep_1(sK3,sK4)
    | ~ spl6_60
    | ~ spl6_80 ),
    inference(forward_demodulation,[],[f1177,f533])).

fof(f1177,plain,
    ( ~ r1_tsep_1(sK4,sK5)
    | r1_tsep_1(sK3,sK4)
    | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) = k2_tsep_1(sK2,sK4,sK3)
    | ~ spl6_60 ),
    inference(resolution,[],[f421,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ r1_tsep_1(X1,X3)
      | r1_tsep_1(X0,X1)
      | k2_tsep_1(X2,X1,k1_tsep_1(X2,X0,X3)) = k2_tsep_1(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f918,plain,
    ( ~ spl6_3
    | spl6_18
    | spl6_107
    | ~ spl6_40
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f917,f531,f292,f895,f151,f72])).

fof(f151,plain,
    ( spl6_18
  <=> r1_tsep_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f895,plain,
    ( spl6_107
  <=> k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) = k2_tsep_1(sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).

fof(f292,plain,
    ( spl6_40
  <=> sP0(sK3,sK4,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f917,plain,
    ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) = k2_tsep_1(sK2,sK3,sK4)
    | r1_tsep_1(sK4,sK3)
    | ~ r1_tsep_1(sK4,sK5)
    | ~ spl6_40
    | ~ spl6_80 ),
    inference(forward_demodulation,[],[f892,f533])).

fof(f892,plain,
    ( r1_tsep_1(sK4,sK3)
    | ~ r1_tsep_1(sK4,sK5)
    | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) = k2_tsep_1(sK2,sK4,sK3)
    | ~ spl6_40 ),
    inference(resolution,[],[f294,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X1,X3)
      | k2_tsep_1(X2,X1,X0) = k2_tsep_1(X2,X1,k1_tsep_1(X2,X3,X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k2_tsep_1(X2,X1,X0) = k2_tsep_1(X2,X1,k1_tsep_1(X2,X3,X0))
        & k2_tsep_1(X2,X0,X1) = k2_tsep_1(X2,k1_tsep_1(X2,X3,X0),X1) )
      | ( r1_tsep_1(X1,X0)
        & r1_tsep_1(X0,X1) )
      | ( ~ r1_tsep_1(X1,X3)
        & ~ r1_tsep_1(X3,X1) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X3,X2,X0,X1] :
      ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X3)
        & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X3,X2) )
      | ( r1_tsep_1(X2,X3)
        & r1_tsep_1(X3,X2) )
      | ( ~ r1_tsep_1(X2,X1)
        & ~ r1_tsep_1(X1,X2) )
      | ~ sP0(X3,X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X3,X2,X0,X1] :
      ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X3)
        & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X3,X2) )
      | ( r1_tsep_1(X2,X3)
        & r1_tsep_1(X3,X2) )
      | ( ~ r1_tsep_1(X2,X1)
        & ~ r1_tsep_1(X1,X2) )
      | ~ sP0(X3,X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f294,plain,
    ( sP0(sK3,sK4,sK2,sK5)
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f292])).

fof(f916,plain,
    ( ~ spl6_4
    | spl6_18
    | spl6_107
    | ~ spl6_40
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f915,f531,f292,f895,f151,f76])).

fof(f915,plain,
    ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) = k2_tsep_1(sK2,sK3,sK4)
    | r1_tsep_1(sK4,sK3)
    | ~ r1_tsep_1(sK5,sK4)
    | ~ spl6_40
    | ~ spl6_80 ),
    inference(forward_demodulation,[],[f891,f533])).

fof(f891,plain,
    ( r1_tsep_1(sK4,sK3)
    | ~ r1_tsep_1(sK5,sK4)
    | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) = k2_tsep_1(sK2,sK4,sK3)
    | ~ spl6_40 ),
    inference(resolution,[],[f294,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X3,X1)
      | k2_tsep_1(X2,X1,X0) = k2_tsep_1(X2,X1,k1_tsep_1(X2,X3,X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f534,plain,
    ( spl6_80
    | ~ spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14
    | spl6_18
    | ~ spl6_77 ),
    inference(avatar_split_clause,[],[f529,f513,f151,f126,f121,f116,f111,f106,f101,f96,f81,f531])).

fof(f81,plain,
    ( spl6_5
  <=> m1_pre_topc(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f96,plain,
    ( spl6_8
  <=> m1_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f101,plain,
    ( spl6_9
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f106,plain,
    ( spl6_10
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f111,plain,
    ( spl6_11
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f116,plain,
    ( spl6_12
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f121,plain,
    ( spl6_13
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f126,plain,
    ( spl6_14
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f513,plain,
    ( spl6_77
  <=> g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f529,plain,
    ( k2_tsep_1(sK2,sK3,sK4) = k2_tsep_1(sK2,sK4,sK3)
    | ~ spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14
    | spl6_18
    | ~ spl6_77 ),
    inference(forward_demodulation,[],[f527,f515])).

fof(f515,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK3,sK4)
    | ~ spl6_77 ),
    inference(avatar_component_clause,[],[f513])).

fof(f527,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK4,sK3)
    | ~ spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14
    | spl6_18 ),
    inference(unit_resulting_resolution,[],[f128,f123,f118,f103,f113,f98,f108,f153,f83,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X2,X1)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X2,X1) )
                & ( m1_pre_topc(X1,X2)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_pre_topc(X1,X2) ) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X2,X1)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X2,X1) )
                & ( m1_pre_topc(X1,X2)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_pre_topc(X1,X2) ) )
              | r1_tsep_1(X1,X2)
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
             => ( ~ r1_tsep_1(X1,X2)
               => ( ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => m1_pre_topc(X2,X1) )
                  & ( m1_pre_topc(X2,X1)
                   => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                  & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                   => m1_pre_topc(X1,X2) )
                  & ( m1_pre_topc(X1,X2)
                   => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tsep_1)).

fof(f83,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f153,plain,
    ( ~ r1_tsep_1(sK4,sK3)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f151])).

fof(f108,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f98,plain,
    ( m1_pre_topc(sK4,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f113,plain,
    ( ~ v2_struct_0(sK3)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f103,plain,
    ( ~ v2_struct_0(sK4)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f118,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f116])).

fof(f123,plain,
    ( v2_pre_topc(sK2)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f128,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f526,plain,
    ( ~ spl6_79
    | spl6_1
    | ~ spl6_77 ),
    inference(avatar_split_clause,[],[f521,f513,f63,f523])).

fof(f63,plain,
    ( spl6_1
  <=> g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f521,plain,
    ( k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) != k2_tsep_1(sK2,sK3,sK4)
    | spl6_1
    | ~ spl6_77 ),
    inference(backward_demodulation,[],[f65,f515])).

fof(f65,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f516,plain,
    ( spl6_77
    | ~ spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14
    | spl6_15 ),
    inference(avatar_split_clause,[],[f510,f134,f126,f121,f116,f111,f106,f101,f96,f81,f513])).

fof(f510,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK3,sK4)
    | ~ spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14
    | spl6_15 ),
    inference(unit_resulting_resolution,[],[f128,f123,f118,f113,f103,f108,f98,f136,f83,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f136,plain,
    ( ~ r1_tsep_1(sK3,sK4)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f134])).

fof(f422,plain,
    ( spl6_60
    | ~ spl6_6
    | spl6_7
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14 ),
    inference(avatar_split_clause,[],[f350,f126,f121,f116,f111,f106,f101,f96,f91,f86,f419])).

fof(f86,plain,
    ( spl6_6
  <=> m1_pre_topc(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f91,plain,
    ( spl6_7
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f350,plain,
    ( sP1(sK3,sK4,sK2,sK5)
    | ~ spl6_6
    | spl6_7
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f128,f123,f93,f113,f108,f103,f98,f88,f118,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | sP1(X1,X2,X0,X3)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( sP1(X1,X2,X0,X3)
                    & sP0(X3,X2,X0,X1) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f9,f15,f14])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X1)
                        & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X1,X2) )
                      | ( ~ r1_tsep_1(X2,X3)
                        & ~ r1_tsep_1(X3,X2) )
                      | ( r1_tsep_1(X2,X1)
                        & r1_tsep_1(X1,X2) ) )
                    & ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X3)
                        & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X3,X2) )
                      | ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X3,X2) )
                      | ( ~ r1_tsep_1(X2,X1)
                        & ~ r1_tsep_1(X1,X2) ) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X1)
                        & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X1,X2) )
                      | ( ~ r1_tsep_1(X2,X3)
                        & ~ r1_tsep_1(X3,X2) )
                      | ( r1_tsep_1(X2,X1)
                        & r1_tsep_1(X1,X2) ) )
                    & ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X3)
                        & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X3,X2) )
                      | ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X3,X2) )
                      | ( ~ r1_tsep_1(X2,X1)
                        & ~ r1_tsep_1(X1,X2) ) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ ( ~ ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X1)
                            & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X1,X2) )
                        & ( r1_tsep_1(X2,X3)
                          | r1_tsep_1(X3,X2) )
                        & ~ ( r1_tsep_1(X2,X1)
                            & r1_tsep_1(X1,X2) ) )
                    & ~ ( ~ ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X3)
                            & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X3,X2) )
                        & ~ ( r1_tsep_1(X2,X3)
                            & r1_tsep_1(X3,X2) )
                        & ( r1_tsep_1(X2,X1)
                          | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tmap_1)).

fof(f88,plain,
    ( m1_pre_topc(sK5,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f93,plain,
    ( ~ v2_struct_0(sK5)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f295,plain,
    ( spl6_40
    | ~ spl6_6
    | spl6_7
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14 ),
    inference(avatar_split_clause,[],[f175,f126,f121,f116,f111,f106,f101,f96,f91,f86,f292])).

fof(f175,plain,
    ( sP0(sK3,sK4,sK2,sK5)
    | ~ spl6_6
    | spl6_7
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f128,f123,f113,f93,f88,f103,f98,f108,f118,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | sP0(X3,X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f154,plain,
    ( ~ spl6_18
    | ~ spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14 ),
    inference(avatar_split_clause,[],[f148,f126,f121,f116,f111,f106,f101,f96,f81,f151])).

fof(f148,plain,
    ( ~ r1_tsep_1(sK4,sK3)
    | ~ spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f128,f123,f103,f113,f108,f83,f98,f118,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(X2,X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f137,plain,
    ( ~ spl6_15
    | ~ spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14 ),
    inference(avatar_split_clause,[],[f131,f126,f121,f116,f111,f106,f101,f96,f81,f134])).

fof(f131,plain,
    ( ~ r1_tsep_1(sK3,sK4)
    | ~ spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f128,f123,f103,f113,f108,f83,f98,f118,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(X1,X2)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f129,plain,(
    ~ spl6_14 ),
    inference(avatar_split_clause,[],[f26,f126])).

fof(f26,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3))
      | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) )
    & ( r1_tsep_1(sK5,sK4)
      | r1_tsep_1(sK4,sK5) )
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f7,f20,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                      | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                    & ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & m1_pre_topc(X1,X2)
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
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X3,X1))
                    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X1,X3)) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X3,X1))
                  | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X1,X3)) )
                & ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK2)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X3,sK3))
                | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,X2,k1_tsep_1(sK2,sK3,X3)) )
              & ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & m1_pre_topc(sK3,X2)
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK2)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK3,sK2)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X3,sK3))
              | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,X2,k1_tsep_1(sK2,sK3,X3)) )
            & ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & m1_pre_topc(sK3,X2)
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,X3,sK3))
            | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,X3)) )
          & ( r1_tsep_1(X3,sK4)
            | r1_tsep_1(sK4,X3) )
          & m1_pre_topc(sK3,sK4)
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,X3,sK3))
          | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,X3)) )
        & ( r1_tsep_1(X3,sK4)
          | r1_tsep_1(sK4,X3) )
        & m1_pre_topc(sK3,sK4)
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3))
        | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) )
      & ( r1_tsep_1(sK5,sK4)
        | r1_tsep_1(sK4,sK5) )
      & m1_pre_topc(sK3,sK4)
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                    | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                    | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
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
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                          & k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
                   => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                        & k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tmap_1)).

fof(f124,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f27,f121])).

fof(f27,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f119,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f28,f116])).

fof(f28,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f114,plain,(
    ~ spl6_11 ),
    inference(avatar_split_clause,[],[f29,f111])).

fof(f29,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f109,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f30,f106])).

fof(f30,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f104,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f31,f101])).

fof(f31,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f99,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f32,f96])).

fof(f32,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f94,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f33,f91])).

fof(f33,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f89,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f34,f86])).

fof(f34,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f35,f81])).

fof(f35,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f79,plain,
    ( spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f36,f76,f72])).

fof(f36,plain,
    ( r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f37,f67,f63])).

fof(f67,plain,
    ( spl6_2
  <=> g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f37,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3))
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.47  % (13245)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.19/0.48  % (13259)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.19/0.48  % (13244)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.19/0.48  % (13239)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.19/0.48  % (13249)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.19/0.49  % (13251)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.19/0.49  % (13243)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.19/0.49  % (13240)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.19/0.49  % (13262)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.19/0.50  % (13242)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.19/0.50  % (13254)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.19/0.50  % (13260)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.19/0.50  % (13261)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.19/0.50  % (13246)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.50  % (13252)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.19/0.50  % (13253)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.19/0.50  % (13262)Refutation not found, incomplete strategy% (13262)------------------------------
% 0.19/0.50  % (13262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (13262)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (13262)Memory used [KB]: 10618
% 0.19/0.50  % (13262)Time elapsed: 0.065 s
% 0.19/0.50  % (13262)------------------------------
% 0.19/0.50  % (13262)------------------------------
% 0.19/0.51  % (13258)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.19/0.51  % (13255)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.19/0.51  % (13242)Refutation not found, incomplete strategy% (13242)------------------------------
% 0.19/0.51  % (13242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (13246)Refutation not found, incomplete strategy% (13246)------------------------------
% 0.19/0.51  % (13246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (13246)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (13246)Memory used [KB]: 6140
% 0.19/0.51  % (13246)Time elapsed: 0.071 s
% 0.19/0.51  % (13246)------------------------------
% 0.19/0.51  % (13246)------------------------------
% 0.19/0.51  % (13247)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.19/0.51  % (13257)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.19/0.51  % (13250)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.19/0.51  % (13245)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.52  % (13242)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (13242)Memory used [KB]: 10618
% 0.19/0.52  % (13242)Time elapsed: 0.104 s
% 0.19/0.52  % (13242)------------------------------
% 0.19/0.52  % (13242)------------------------------
% 0.19/0.53  fof(f1203,plain,(
% 0.19/0.53    $false),
% 0.19/0.53    inference(avatar_sat_refutation,[],[f70,f79,f84,f89,f94,f99,f104,f109,f114,f119,f124,f129,f137,f154,f295,f422,f516,f526,f534,f916,f918,f1195,f1199,f1202])).
% 0.19/0.53  fof(f1202,plain,(
% 0.19/0.53    k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) != k2_tsep_1(sK2,sK3,sK4) | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK3,sK4) | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3))),
% 0.19/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.53  fof(f1199,plain,(
% 0.19/0.53    spl6_15 | ~spl6_4 | spl6_79 | ~spl6_60 | ~spl6_80),
% 0.19/0.53    inference(avatar_split_clause,[],[f1198,f531,f419,f523,f76,f134])).
% 0.19/0.53  fof(f134,plain,(
% 0.19/0.53    spl6_15 <=> r1_tsep_1(sK3,sK4)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.19/0.53  fof(f76,plain,(
% 0.19/0.53    spl6_4 <=> r1_tsep_1(sK5,sK4)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.19/0.53  fof(f523,plain,(
% 0.19/0.53    spl6_79 <=> k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) = k2_tsep_1(sK2,sK3,sK4)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).
% 0.19/0.53  fof(f419,plain,(
% 0.19/0.53    spl6_60 <=> sP1(sK3,sK4,sK2,sK5)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 0.19/0.53  fof(f531,plain,(
% 0.19/0.53    spl6_80 <=> k2_tsep_1(sK2,sK3,sK4) = k2_tsep_1(sK2,sK4,sK3)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).
% 0.19/0.53  fof(f1198,plain,(
% 0.19/0.53    k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) = k2_tsep_1(sK2,sK3,sK4) | ~r1_tsep_1(sK5,sK4) | r1_tsep_1(sK3,sK4) | (~spl6_60 | ~spl6_80)),
% 0.19/0.53    inference(forward_demodulation,[],[f1179,f533])).
% 0.19/0.53  fof(f533,plain,(
% 0.19/0.53    k2_tsep_1(sK2,sK3,sK4) = k2_tsep_1(sK2,sK4,sK3) | ~spl6_80),
% 0.19/0.53    inference(avatar_component_clause,[],[f531])).
% 0.19/0.53  fof(f1179,plain,(
% 0.19/0.53    ~r1_tsep_1(sK5,sK4) | r1_tsep_1(sK3,sK4) | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) = k2_tsep_1(sK2,sK4,sK3) | ~spl6_60),
% 0.19/0.53    inference(resolution,[],[f421,f42])).
% 0.19/0.53  fof(f42,plain,(
% 0.19/0.53    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | ~r1_tsep_1(X3,X1) | r1_tsep_1(X0,X1) | k2_tsep_1(X2,X1,k1_tsep_1(X2,X0,X3)) = k2_tsep_1(X2,X1,X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f23])).
% 0.19/0.53  fof(f23,plain,(
% 0.19/0.53    ! [X0,X1,X2,X3] : ((k2_tsep_1(X2,X1,k1_tsep_1(X2,X0,X3)) = k2_tsep_1(X2,X1,X0) & k2_tsep_1(X2,k1_tsep_1(X2,X0,X3),X1) = k2_tsep_1(X2,X0,X1)) | (~r1_tsep_1(X1,X3) & ~r1_tsep_1(X3,X1)) | (r1_tsep_1(X1,X0) & r1_tsep_1(X0,X1)) | ~sP1(X0,X1,X2,X3))),
% 0.19/0.53    inference(rectify,[],[f22])).
% 0.19/0.53  fof(f22,plain,(
% 0.19/0.53    ! [X1,X2,X0,X3] : ((k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X1) & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X1,X2)) | (~r1_tsep_1(X2,X3) & ~r1_tsep_1(X3,X2)) | (r1_tsep_1(X2,X1) & r1_tsep_1(X1,X2)) | ~sP1(X1,X2,X0,X3))),
% 0.19/0.53    inference(nnf_transformation,[],[f15])).
% 0.19/0.53  fof(f15,plain,(
% 0.19/0.53    ! [X1,X2,X0,X3] : ((k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X1) & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X1,X2)) | (~r1_tsep_1(X2,X3) & ~r1_tsep_1(X3,X2)) | (r1_tsep_1(X2,X1) & r1_tsep_1(X1,X2)) | ~sP1(X1,X2,X0,X3))),
% 0.19/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.19/0.53  fof(f421,plain,(
% 0.19/0.53    sP1(sK3,sK4,sK2,sK5) | ~spl6_60),
% 0.19/0.53    inference(avatar_component_clause,[],[f419])).
% 0.19/0.53  fof(f1195,plain,(
% 0.19/0.53    spl6_15 | ~spl6_3 | spl6_79 | ~spl6_60 | ~spl6_80),
% 0.19/0.53    inference(avatar_split_clause,[],[f1194,f531,f419,f523,f72,f134])).
% 0.19/0.53  fof(f72,plain,(
% 0.19/0.53    spl6_3 <=> r1_tsep_1(sK4,sK5)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.19/0.53  fof(f1194,plain,(
% 0.19/0.53    k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) = k2_tsep_1(sK2,sK3,sK4) | ~r1_tsep_1(sK4,sK5) | r1_tsep_1(sK3,sK4) | (~spl6_60 | ~spl6_80)),
% 0.19/0.53    inference(forward_demodulation,[],[f1177,f533])).
% 0.19/0.53  fof(f1177,plain,(
% 0.19/0.53    ~r1_tsep_1(sK4,sK5) | r1_tsep_1(sK3,sK4) | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) = k2_tsep_1(sK2,sK4,sK3) | ~spl6_60),
% 0.19/0.53    inference(resolution,[],[f421,f44])).
% 0.19/0.53  fof(f44,plain,(
% 0.19/0.53    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | ~r1_tsep_1(X1,X3) | r1_tsep_1(X0,X1) | k2_tsep_1(X2,X1,k1_tsep_1(X2,X0,X3)) = k2_tsep_1(X2,X1,X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f23])).
% 0.19/0.53  fof(f918,plain,(
% 0.19/0.53    ~spl6_3 | spl6_18 | spl6_107 | ~spl6_40 | ~spl6_80),
% 0.19/0.53    inference(avatar_split_clause,[],[f917,f531,f292,f895,f151,f72])).
% 0.19/0.53  fof(f151,plain,(
% 0.19/0.53    spl6_18 <=> r1_tsep_1(sK4,sK3)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.19/0.53  fof(f895,plain,(
% 0.19/0.53    spl6_107 <=> k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) = k2_tsep_1(sK2,sK3,sK4)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).
% 0.19/0.53  fof(f292,plain,(
% 0.19/0.53    spl6_40 <=> sP0(sK3,sK4,sK2,sK5)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.19/0.53  fof(f917,plain,(
% 0.19/0.53    k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) = k2_tsep_1(sK2,sK3,sK4) | r1_tsep_1(sK4,sK3) | ~r1_tsep_1(sK4,sK5) | (~spl6_40 | ~spl6_80)),
% 0.19/0.53    inference(forward_demodulation,[],[f892,f533])).
% 0.19/0.53  fof(f892,plain,(
% 0.19/0.53    r1_tsep_1(sK4,sK3) | ~r1_tsep_1(sK4,sK5) | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) = k2_tsep_1(sK2,sK4,sK3) | ~spl6_40),
% 0.19/0.53    inference(resolution,[],[f294,f53])).
% 0.19/0.53  fof(f53,plain,(
% 0.19/0.53    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r1_tsep_1(X1,X0) | ~r1_tsep_1(X1,X3) | k2_tsep_1(X2,X1,X0) = k2_tsep_1(X2,X1,k1_tsep_1(X2,X3,X0))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f25])).
% 0.19/0.53  fof(f25,plain,(
% 0.19/0.53    ! [X0,X1,X2,X3] : ((k2_tsep_1(X2,X1,X0) = k2_tsep_1(X2,X1,k1_tsep_1(X2,X3,X0)) & k2_tsep_1(X2,X0,X1) = k2_tsep_1(X2,k1_tsep_1(X2,X3,X0),X1)) | (r1_tsep_1(X1,X0) & r1_tsep_1(X0,X1)) | (~r1_tsep_1(X1,X3) & ~r1_tsep_1(X3,X1)) | ~sP0(X0,X1,X2,X3))),
% 0.19/0.53    inference(rectify,[],[f24])).
% 0.19/0.53  fof(f24,plain,(
% 0.19/0.53    ! [X3,X2,X0,X1] : ((k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X3) & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X3,X2)) | (r1_tsep_1(X2,X3) & r1_tsep_1(X3,X2)) | (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~sP0(X3,X2,X0,X1))),
% 0.19/0.53    inference(nnf_transformation,[],[f14])).
% 0.19/0.53  fof(f14,plain,(
% 0.19/0.53    ! [X3,X2,X0,X1] : ((k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X3) & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X3,X2)) | (r1_tsep_1(X2,X3) & r1_tsep_1(X3,X2)) | (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~sP0(X3,X2,X0,X1))),
% 0.19/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.53  fof(f294,plain,(
% 0.19/0.53    sP0(sK3,sK4,sK2,sK5) | ~spl6_40),
% 0.19/0.53    inference(avatar_component_clause,[],[f292])).
% 0.19/0.53  fof(f916,plain,(
% 0.19/0.53    ~spl6_4 | spl6_18 | spl6_107 | ~spl6_40 | ~spl6_80),
% 0.19/0.53    inference(avatar_split_clause,[],[f915,f531,f292,f895,f151,f76])).
% 0.19/0.53  fof(f915,plain,(
% 0.19/0.53    k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) = k2_tsep_1(sK2,sK3,sK4) | r1_tsep_1(sK4,sK3) | ~r1_tsep_1(sK5,sK4) | (~spl6_40 | ~spl6_80)),
% 0.19/0.53    inference(forward_demodulation,[],[f891,f533])).
% 0.19/0.53  fof(f891,plain,(
% 0.19/0.53    r1_tsep_1(sK4,sK3) | ~r1_tsep_1(sK5,sK4) | k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) = k2_tsep_1(sK2,sK4,sK3) | ~spl6_40),
% 0.19/0.53    inference(resolution,[],[f294,f52])).
% 0.19/0.53  fof(f52,plain,(
% 0.19/0.53    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r1_tsep_1(X1,X0) | ~r1_tsep_1(X3,X1) | k2_tsep_1(X2,X1,X0) = k2_tsep_1(X2,X1,k1_tsep_1(X2,X3,X0))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f25])).
% 0.19/0.53  fof(f534,plain,(
% 0.19/0.53    spl6_80 | ~spl6_5 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_11 | ~spl6_12 | ~spl6_13 | spl6_14 | spl6_18 | ~spl6_77),
% 0.19/0.53    inference(avatar_split_clause,[],[f529,f513,f151,f126,f121,f116,f111,f106,f101,f96,f81,f531])).
% 0.19/0.53  fof(f81,plain,(
% 0.19/0.53    spl6_5 <=> m1_pre_topc(sK3,sK4)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.19/0.53  fof(f96,plain,(
% 0.19/0.53    spl6_8 <=> m1_pre_topc(sK4,sK2)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.19/0.53  fof(f101,plain,(
% 0.19/0.53    spl6_9 <=> v2_struct_0(sK4)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.19/0.53  fof(f106,plain,(
% 0.19/0.53    spl6_10 <=> m1_pre_topc(sK3,sK2)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.19/0.53  fof(f111,plain,(
% 0.19/0.53    spl6_11 <=> v2_struct_0(sK3)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.19/0.53  fof(f116,plain,(
% 0.19/0.53    spl6_12 <=> l1_pre_topc(sK2)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.19/0.53  fof(f121,plain,(
% 0.19/0.53    spl6_13 <=> v2_pre_topc(sK2)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.19/0.53  fof(f126,plain,(
% 0.19/0.53    spl6_14 <=> v2_struct_0(sK2)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.19/0.53  fof(f513,plain,(
% 0.19/0.53    spl6_77 <=> g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK3,sK4)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).
% 0.19/0.53  fof(f529,plain,(
% 0.19/0.53    k2_tsep_1(sK2,sK3,sK4) = k2_tsep_1(sK2,sK4,sK3) | (~spl6_5 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_11 | ~spl6_12 | ~spl6_13 | spl6_14 | spl6_18 | ~spl6_77)),
% 0.19/0.53    inference(forward_demodulation,[],[f527,f515])).
% 0.19/0.53  fof(f515,plain,(
% 0.19/0.53    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK3,sK4) | ~spl6_77),
% 0.19/0.53    inference(avatar_component_clause,[],[f513])).
% 0.19/0.53  fof(f527,plain,(
% 0.19/0.53    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK4,sK3) | (~spl6_5 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_11 | ~spl6_12 | ~spl6_13 | spl6_14 | spl6_18)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f128,f123,f118,f103,f113,f98,f108,f153,f83,f58])).
% 0.19/0.53  fof(f58,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X1) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f11])).
% 0.19/0.53  fof(f11,plain,(
% 0.19/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X2,X1) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X2,X1)) & (m1_pre_topc(X1,X2) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X2))) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.53    inference(flattening,[],[f10])).
% 0.19/0.53  fof(f10,plain,(
% 0.19/0.53    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X2,X1) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X2,X1)) & (m1_pre_topc(X1,X2) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X2))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f3])).
% 0.19/0.53  fof(f3,axiom,(
% 0.19/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ((k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => m1_pre_topc(X2,X1)) & (m1_pre_topc(X2,X1) => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) => m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tsep_1)).
% 0.19/0.53  fof(f83,plain,(
% 0.19/0.53    m1_pre_topc(sK3,sK4) | ~spl6_5),
% 0.19/0.53    inference(avatar_component_clause,[],[f81])).
% 0.19/0.53  fof(f153,plain,(
% 0.19/0.53    ~r1_tsep_1(sK4,sK3) | spl6_18),
% 0.19/0.53    inference(avatar_component_clause,[],[f151])).
% 0.19/0.53  fof(f108,plain,(
% 0.19/0.53    m1_pre_topc(sK3,sK2) | ~spl6_10),
% 0.19/0.53    inference(avatar_component_clause,[],[f106])).
% 0.19/0.53  fof(f98,plain,(
% 0.19/0.53    m1_pre_topc(sK4,sK2) | ~spl6_8),
% 0.19/0.53    inference(avatar_component_clause,[],[f96])).
% 0.19/0.53  fof(f113,plain,(
% 0.19/0.53    ~v2_struct_0(sK3) | spl6_11),
% 0.19/0.53    inference(avatar_component_clause,[],[f111])).
% 0.19/0.53  fof(f103,plain,(
% 0.19/0.53    ~v2_struct_0(sK4) | spl6_9),
% 0.19/0.53    inference(avatar_component_clause,[],[f101])).
% 0.19/0.53  fof(f118,plain,(
% 0.19/0.53    l1_pre_topc(sK2) | ~spl6_12),
% 0.19/0.53    inference(avatar_component_clause,[],[f116])).
% 0.19/0.53  fof(f123,plain,(
% 0.19/0.53    v2_pre_topc(sK2) | ~spl6_13),
% 0.19/0.53    inference(avatar_component_clause,[],[f121])).
% 0.19/0.53  fof(f128,plain,(
% 0.19/0.53    ~v2_struct_0(sK2) | spl6_14),
% 0.19/0.53    inference(avatar_component_clause,[],[f126])).
% 0.19/0.53  fof(f526,plain,(
% 0.19/0.53    ~spl6_79 | spl6_1 | ~spl6_77),
% 0.19/0.53    inference(avatar_split_clause,[],[f521,f513,f63,f523])).
% 0.19/0.53  fof(f63,plain,(
% 0.19/0.53    spl6_1 <=> g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5))),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.19/0.53  fof(f521,plain,(
% 0.19/0.53    k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) != k2_tsep_1(sK2,sK3,sK4) | (spl6_1 | ~spl6_77)),
% 0.19/0.53    inference(backward_demodulation,[],[f65,f515])).
% 0.19/0.53  fof(f65,plain,(
% 0.19/0.53    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5)) | spl6_1),
% 0.19/0.53    inference(avatar_component_clause,[],[f63])).
% 0.19/0.53  fof(f516,plain,(
% 0.19/0.53    spl6_77 | ~spl6_5 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_11 | ~spl6_12 | ~spl6_13 | spl6_14 | spl6_15),
% 0.19/0.53    inference(avatar_split_clause,[],[f510,f134,f126,f121,f116,f111,f106,f101,f96,f81,f513])).
% 0.19/0.53  fof(f510,plain,(
% 0.19/0.53    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK3,sK4) | (~spl6_5 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_11 | ~spl6_12 | ~spl6_13 | spl6_14 | spl6_15)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f128,f123,f118,f113,f103,f108,f98,f136,f83,f56])).
% 0.19/0.53  fof(f56,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X2) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f11])).
% 0.19/0.53  fof(f136,plain,(
% 0.19/0.53    ~r1_tsep_1(sK3,sK4) | spl6_15),
% 0.19/0.53    inference(avatar_component_clause,[],[f134])).
% 0.19/0.53  fof(f422,plain,(
% 0.19/0.53    spl6_60 | ~spl6_6 | spl6_7 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_11 | ~spl6_12 | ~spl6_13 | spl6_14),
% 0.19/0.53    inference(avatar_split_clause,[],[f350,f126,f121,f116,f111,f106,f101,f96,f91,f86,f419])).
% 0.19/0.53  fof(f86,plain,(
% 0.19/0.53    spl6_6 <=> m1_pre_topc(sK5,sK2)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.19/0.53  fof(f91,plain,(
% 0.19/0.53    spl6_7 <=> v2_struct_0(sK5)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.19/0.53  fof(f350,plain,(
% 0.19/0.53    sP1(sK3,sK4,sK2,sK5) | (~spl6_6 | spl6_7 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_11 | ~spl6_12 | ~spl6_13 | spl6_14)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f128,f123,f93,f113,f108,f103,f98,f88,f118,f55])).
% 0.19/0.53  fof(f55,plain,(
% 0.19/0.53    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | sP1(X1,X2,X0,X3) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f16])).
% 0.19/0.53  fof(f16,plain,(
% 0.19/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((sP1(X1,X2,X0,X3) & sP0(X3,X2,X0,X1)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.53    inference(definition_folding,[],[f9,f15,f14])).
% 0.19/0.53  fof(f9,plain,(
% 0.19/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X1) & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X1,X2)) | (~r1_tsep_1(X2,X3) & ~r1_tsep_1(X3,X2)) | (r1_tsep_1(X2,X1) & r1_tsep_1(X1,X2))) & ((k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X3) & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X3,X2)) | (r1_tsep_1(X2,X3) & r1_tsep_1(X3,X2)) | (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.53    inference(flattening,[],[f8])).
% 0.19/0.53  fof(f8,plain,(
% 0.19/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X1) & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X1,X2)) | (~r1_tsep_1(X2,X3) & ~r1_tsep_1(X3,X2)) | (r1_tsep_1(X2,X1) & r1_tsep_1(X1,X2))) & ((k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X3) & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X3,X2)) | (r1_tsep_1(X2,X3) & r1_tsep_1(X3,X2)) | (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f2])).
% 0.19/0.53  fof(f2,axiom,(
% 0.19/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~(~(k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X1) & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X1,X2)) & (r1_tsep_1(X2,X3) | r1_tsep_1(X3,X2)) & ~(r1_tsep_1(X2,X1) & r1_tsep_1(X1,X2))) & ~(~(k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X3) & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X3,X2)) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X3,X2)) & (r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2))))))))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tmap_1)).
% 0.19/0.53  fof(f88,plain,(
% 0.19/0.53    m1_pre_topc(sK5,sK2) | ~spl6_6),
% 0.19/0.53    inference(avatar_component_clause,[],[f86])).
% 0.19/0.53  fof(f93,plain,(
% 0.19/0.53    ~v2_struct_0(sK5) | spl6_7),
% 0.19/0.53    inference(avatar_component_clause,[],[f91])).
% 0.19/0.53  fof(f295,plain,(
% 0.19/0.53    spl6_40 | ~spl6_6 | spl6_7 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_11 | ~spl6_12 | ~spl6_13 | spl6_14),
% 0.19/0.53    inference(avatar_split_clause,[],[f175,f126,f121,f116,f111,f106,f101,f96,f91,f86,f292])).
% 0.19/0.53  fof(f175,plain,(
% 0.19/0.53    sP0(sK3,sK4,sK2,sK5) | (~spl6_6 | spl6_7 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_11 | ~spl6_12 | ~spl6_13 | spl6_14)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f128,f123,f113,f93,f88,f103,f98,f108,f118,f54])).
% 0.19/0.53  fof(f54,plain,(
% 0.19/0.53    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | sP0(X3,X2,X0,X1) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f16])).
% 0.19/0.53  fof(f154,plain,(
% 0.19/0.53    ~spl6_18 | ~spl6_5 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_11 | ~spl6_12 | ~spl6_13 | spl6_14),
% 0.19/0.53    inference(avatar_split_clause,[],[f148,f126,f121,f116,f111,f106,f101,f96,f81,f151])).
% 0.19/0.53  fof(f148,plain,(
% 0.19/0.53    ~r1_tsep_1(sK4,sK3) | (~spl6_5 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_11 | ~spl6_12 | ~spl6_13 | spl6_14)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f128,f123,f103,f113,f108,f83,f98,f118,f61])).
% 0.19/0.53  fof(f61,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~r1_tsep_1(X2,X1) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f13])).
% 0.19/0.53  fof(f13,plain,(
% 0.19/0.53    ! [X0] : (! [X1] : (! [X2] : ((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.53    inference(flattening,[],[f12])).
% 0.19/0.53  fof(f12,plain,(
% 0.19/0.53    ! [X0] : (! [X1] : (! [X2] : (((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f1])).
% 0.19/0.53  fof(f1,axiom,(
% 0.19/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).
% 0.19/0.53  fof(f137,plain,(
% 0.19/0.53    ~spl6_15 | ~spl6_5 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_11 | ~spl6_12 | ~spl6_13 | spl6_14),
% 0.19/0.53    inference(avatar_split_clause,[],[f131,f126,f121,f116,f111,f106,f101,f96,f81,f134])).
% 0.19/0.53  fof(f131,plain,(
% 0.19/0.53    ~r1_tsep_1(sK3,sK4) | (~spl6_5 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_11 | ~spl6_12 | ~spl6_13 | spl6_14)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f128,f123,f103,f113,f108,f83,f98,f118,f60])).
% 0.19/0.53  fof(f60,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~r1_tsep_1(X1,X2) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f13])).
% 0.19/0.53  fof(f129,plain,(
% 0.19/0.53    ~spl6_14),
% 0.19/0.53    inference(avatar_split_clause,[],[f26,f126])).
% 0.19/0.53  fof(f26,plain,(
% 0.19/0.53    ~v2_struct_0(sK2)),
% 0.19/0.53    inference(cnf_transformation,[],[f21])).
% 0.19/0.53  fof(f21,plain,(
% 0.19/0.53    ((((g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5))) & (r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f7,f20,f19,f18,f17])).
% 0.19/0.53  fof(f17,plain,(
% 0.19/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X3,X1)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X1,X3))) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f18,plain,(
% 0.19/0.53    ? [X1] : (? [X2] : (? [X3] : ((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X3,X1)) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X1,X3))) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X3,sK3)) | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,X2,k1_tsep_1(sK2,sK3,X3))) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(sK3,X2) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f19,plain,(
% 0.19/0.53    ? [X2] : (? [X3] : ((g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,X2,k1_tsep_1(sK2,X3,sK3)) | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,X2,k1_tsep_1(sK2,sK3,X3))) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(sK3,X2) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : ((g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,X3,sK3)) | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,X3))) & (r1_tsep_1(X3,sK4) | r1_tsep_1(sK4,X3)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f20,plain,(
% 0.19/0.53    ? [X3] : ((g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,X3,sK3)) | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,X3))) & (r1_tsep_1(X3,sK4) | r1_tsep_1(sK4,X3)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) => ((g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5))) & (r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f7,plain,(
% 0.19/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.53    inference(flattening,[],[f6])).
% 0.19/0.53  fof(f6,plain,(
% 0.19/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) | k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f5])).
% 0.19/0.53  fof(f5,negated_conjecture,(
% 0.19/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) & k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.19/0.53    inference(negated_conjecture,[],[f4])).
% 0.19/0.53  fof(f4,conjecture,(
% 0.19/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) & k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tmap_1)).
% 0.19/0.53  fof(f124,plain,(
% 0.19/0.53    spl6_13),
% 0.19/0.53    inference(avatar_split_clause,[],[f27,f121])).
% 0.19/0.53  fof(f27,plain,(
% 0.19/0.53    v2_pre_topc(sK2)),
% 0.19/0.53    inference(cnf_transformation,[],[f21])).
% 0.19/0.53  fof(f119,plain,(
% 0.19/0.53    spl6_12),
% 0.19/0.53    inference(avatar_split_clause,[],[f28,f116])).
% 0.19/0.53  fof(f28,plain,(
% 0.19/0.53    l1_pre_topc(sK2)),
% 0.19/0.53    inference(cnf_transformation,[],[f21])).
% 0.19/0.53  fof(f114,plain,(
% 0.19/0.53    ~spl6_11),
% 0.19/0.53    inference(avatar_split_clause,[],[f29,f111])).
% 0.19/0.53  fof(f29,plain,(
% 0.19/0.53    ~v2_struct_0(sK3)),
% 0.19/0.53    inference(cnf_transformation,[],[f21])).
% 0.19/0.53  fof(f109,plain,(
% 0.19/0.53    spl6_10),
% 0.19/0.53    inference(avatar_split_clause,[],[f30,f106])).
% 0.19/0.53  fof(f30,plain,(
% 0.19/0.53    m1_pre_topc(sK3,sK2)),
% 0.19/0.53    inference(cnf_transformation,[],[f21])).
% 0.19/0.53  fof(f104,plain,(
% 0.19/0.53    ~spl6_9),
% 0.19/0.53    inference(avatar_split_clause,[],[f31,f101])).
% 0.19/0.53  fof(f31,plain,(
% 0.19/0.53    ~v2_struct_0(sK4)),
% 0.19/0.53    inference(cnf_transformation,[],[f21])).
% 0.19/0.53  fof(f99,plain,(
% 0.19/0.53    spl6_8),
% 0.19/0.53    inference(avatar_split_clause,[],[f32,f96])).
% 0.19/0.53  fof(f32,plain,(
% 0.19/0.53    m1_pre_topc(sK4,sK2)),
% 0.19/0.53    inference(cnf_transformation,[],[f21])).
% 0.19/0.53  fof(f94,plain,(
% 0.19/0.53    ~spl6_7),
% 0.19/0.53    inference(avatar_split_clause,[],[f33,f91])).
% 0.19/0.53  fof(f33,plain,(
% 0.19/0.53    ~v2_struct_0(sK5)),
% 0.19/0.53    inference(cnf_transformation,[],[f21])).
% 0.19/0.53  fof(f89,plain,(
% 0.19/0.53    spl6_6),
% 0.19/0.53    inference(avatar_split_clause,[],[f34,f86])).
% 0.19/0.53  fof(f34,plain,(
% 0.19/0.53    m1_pre_topc(sK5,sK2)),
% 0.19/0.53    inference(cnf_transformation,[],[f21])).
% 0.19/0.53  fof(f84,plain,(
% 0.19/0.53    spl6_5),
% 0.19/0.53    inference(avatar_split_clause,[],[f35,f81])).
% 0.19/0.53  fof(f35,plain,(
% 0.19/0.53    m1_pre_topc(sK3,sK4)),
% 0.19/0.53    inference(cnf_transformation,[],[f21])).
% 0.19/0.53  fof(f79,plain,(
% 0.19/0.53    spl6_3 | spl6_4),
% 0.19/0.53    inference(avatar_split_clause,[],[f36,f76,f72])).
% 0.19/0.53  fof(f36,plain,(
% 0.19/0.53    r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5)),
% 0.19/0.53    inference(cnf_transformation,[],[f21])).
% 0.19/0.53  fof(f70,plain,(
% 0.19/0.53    ~spl6_1 | ~spl6_2),
% 0.19/0.53    inference(avatar_split_clause,[],[f37,f67,f63])).
% 0.19/0.53  fof(f67,plain,(
% 0.19/0.53    spl6_2 <=> g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3))),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.19/0.53  fof(f37,plain,(
% 0.19/0.53    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK5,sK3)) | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK2,sK4,k1_tsep_1(sK2,sK3,sK5))),
% 0.19/0.53    inference(cnf_transformation,[],[f21])).
% 0.19/0.53  % SZS output end Proof for theBenchmark
% 0.19/0.53  % (13245)------------------------------
% 0.19/0.53  % (13245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (13245)Termination reason: Refutation
% 0.19/0.53  
% 0.19/0.53  % (13245)Memory used [KB]: 11641
% 0.19/0.53  % (13245)Time elapsed: 0.125 s
% 0.19/0.53  % (13245)------------------------------
% 0.19/0.53  % (13245)------------------------------
% 0.19/0.53  % (13238)Success in time 0.184 s
%------------------------------------------------------------------------------
