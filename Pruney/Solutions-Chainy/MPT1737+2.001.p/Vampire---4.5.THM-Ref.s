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
% DateTime   : Thu Dec  3 13:18:10 EST 2020

% Result     : Theorem 4.70s
% Output     : Refutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :  346 ( 778 expanded)
%              Number of leaves         :   70 ( 349 expanded)
%              Depth                    :   12
%              Number of atoms          : 2235 (4204 expanded)
%              Number of equality atoms :   82 ( 145 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3389,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f105,f109,f113,f117,f121,f125,f129,f133,f137,f141,f145,f149,f162,f166,f170,f178,f182,f186,f190,f198,f206,f210,f221,f241,f255,f259,f272,f280,f295,f319,f440,f467,f479,f486,f614,f642,f794,f808,f884,f909,f913,f1321,f1595,f1660,f1695,f2588,f2853,f2867,f2928,f3223,f3281,f3303,f3310,f3330,f3375,f3378,f3388])).

fof(f3388,plain,
    ( ~ spl4_98
    | ~ spl4_6
    | ~ spl4_354 ),
    inference(avatar_split_clause,[],[f3384,f3373,f119,f788])).

fof(f788,plain,
    ( spl4_98
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).

fof(f119,plain,
    ( spl4_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f3373,plain,
    ( spl4_354
  <=> ! [X0] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_354])])).

fof(f3384,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl4_6
    | ~ spl4_354 ),
    inference(resolution,[],[f3374,f120])).

fof(f120,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f3374,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0) )
    | ~ spl4_354 ),
    inference(avatar_component_clause,[],[f3373])).

fof(f3378,plain,
    ( ~ spl4_17
    | spl4_2
    | ~ spl4_11
    | spl4_15
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f293,f278,f154,f139,f103,f160])).

fof(f160,plain,
    ( spl4_17
  <=> v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f103,plain,
    ( spl4_2
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f139,plain,
    ( spl4_11
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f154,plain,
    ( spl4_15
  <=> v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f278,plain,
    ( spl4_38
  <=> ! [X3] :
        ( v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | k1_tsep_1(sK0,sK1,X3) = k1_tsep_1(sK0,X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f293,plain,
    ( ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2))
    | spl4_2
    | ~ spl4_11
    | spl4_15
    | ~ spl4_38 ),
    inference(backward_demodulation,[],[f155,f291])).

fof(f291,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | spl4_2
    | ~ spl4_11
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f287,f104])).

fof(f104,plain,
    ( ~ v2_struct_0(sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f287,plain,
    ( v2_struct_0(sK2)
    | k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | ~ spl4_11
    | ~ spl4_38 ),
    inference(resolution,[],[f279,f140])).

fof(f140,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f139])).

fof(f279,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | k1_tsep_1(sK0,sK1,X3) = k1_tsep_1(sK0,X3,sK1) )
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f278])).

fof(f155,plain,
    ( ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f154])).

fof(f3375,plain,
    ( spl4_354
    | ~ spl4_13
    | spl4_350 ),
    inference(avatar_split_clause,[],[f3346,f3301,f147,f3373])).

fof(f147,plain,
    ( spl4_13
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f3301,plain,
    ( spl4_350
  <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_350])])).

fof(f3346,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_13
    | spl4_350 ),
    inference(resolution,[],[f3302,f148])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f147])).

fof(f3302,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl4_350 ),
    inference(avatar_component_clause,[],[f3301])).

fof(f3330,plain,
    ( spl4_2
    | spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_23
    | spl4_348 ),
    inference(avatar_contradiction_clause,[],[f3329])).

fof(f3329,plain,
    ( $false
    | spl4_2
    | spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_23
    | spl4_348 ),
    inference(subsumption_resolution,[],[f3328,f112])).

fof(f112,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f3328,plain,
    ( v2_struct_0(sK0)
    | spl4_2
    | spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_23
    | spl4_348 ),
    inference(subsumption_resolution,[],[f3327,f140])).

fof(f3327,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl4_2
    | spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_23
    | spl4_348 ),
    inference(subsumption_resolution,[],[f3326,f104])).

fof(f3326,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_23
    | spl4_348 ),
    inference(subsumption_resolution,[],[f3325,f144])).

fof(f144,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_12
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f3325,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_23
    | spl4_348 ),
    inference(subsumption_resolution,[],[f3324,f108])).

fof(f108,plain,
    ( ~ v2_struct_0(sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f3324,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_23
    | spl4_348 ),
    inference(subsumption_resolution,[],[f3323,f120])).

fof(f3323,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl4_5
    | ~ spl4_23
    | spl4_348 ),
    inference(subsumption_resolution,[],[f3320,f116])).

fof(f116,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl4_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f3320,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl4_23
    | spl4_348 ),
    inference(resolution,[],[f3296,f185])).

fof(f185,plain,
    ( ! [X2,X0,X1] :
        ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl4_23
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_pre_topc(k1_tsep_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f3296,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl4_348 ),
    inference(avatar_component_clause,[],[f3295])).

fof(f3295,plain,
    ( spl4_348
  <=> v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_348])])).

fof(f3310,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_18
    | spl4_349 ),
    inference(avatar_contradiction_clause,[],[f3308])).

fof(f3308,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_18
    | spl4_349 ),
    inference(unit_resulting_resolution,[],[f116,f120,f144,f3299,f165])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f3299,plain,
    ( ~ v2_pre_topc(sK1)
    | spl4_349 ),
    inference(avatar_component_clause,[],[f3298])).

fof(f3298,plain,
    ( spl4_349
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_349])])).

fof(f3303,plain,
    ( ~ spl4_348
    | ~ spl4_341
    | ~ spl4_349
    | ~ spl4_350
    | spl4_3
    | ~ spl4_12
    | spl4_17
    | ~ spl4_112
    | ~ spl4_315
    | ~ spl4_347 ),
    inference(avatar_split_clause,[],[f3291,f3279,f2851,f911,f160,f143,f107,f3301,f3298,f3215,f3295])).

fof(f3215,plain,
    ( spl4_341
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_341])])).

fof(f911,plain,
    ( spl4_112
  <=> ! [X1,X0] :
        ( ~ v1_tsep_1(k1_tsep_1(sK0,X0,X0),X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X0),X1)
        | v1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).

fof(f2851,plain,
    ( spl4_315
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_315])])).

fof(f3279,plain,
    ( spl4_347
  <=> v1_tsep_1(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_347])])).

fof(f3291,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl4_3
    | ~ spl4_12
    | spl4_17
    | ~ spl4_112
    | ~ spl4_315
    | ~ spl4_347 ),
    inference(subsumption_resolution,[],[f3290,f108])).

fof(f3290,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ spl4_12
    | spl4_17
    | ~ spl4_112
    | ~ spl4_315
    | ~ spl4_347 ),
    inference(subsumption_resolution,[],[f3289,f144])).

fof(f3289,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | spl4_17
    | ~ spl4_112
    | ~ spl4_315
    | ~ spl4_347 ),
    inference(subsumption_resolution,[],[f3288,f161])).

fof(f161,plain,
    ( ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f160])).

fof(f3288,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ spl4_112
    | ~ spl4_315
    | ~ spl4_347 ),
    inference(subsumption_resolution,[],[f3283,f2852])).

fof(f2852,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_315 ),
    inference(avatar_component_clause,[],[f2851])).

fof(f3283,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2))
    | v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ spl4_112
    | ~ spl4_347 ),
    inference(resolution,[],[f3280,f912])).

fof(f912,plain,
    ( ! [X0,X1] :
        ( ~ v1_tsep_1(k1_tsep_1(sK0,X0,X0),X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X0),X1)
        | v1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl4_112 ),
    inference(avatar_component_clause,[],[f911])).

fof(f3280,plain,
    ( v1_tsep_1(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_347 ),
    inference(avatar_component_clause,[],[f3279])).

fof(f3281,plain,
    ( spl4_314
    | ~ spl4_98
    | spl4_97
    | spl4_347
    | spl4_1
    | spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_27
    | ~ spl4_35
    | ~ spl4_111
    | ~ spl4_202
    | ~ spl4_206 ),
    inference(avatar_split_clause,[],[f1713,f1693,f1658,f907,f257,f204,f143,f131,f127,f123,f119,f115,f111,f107,f99,f3279,f785,f788,f2848])).

fof(f2848,plain,
    ( spl4_314
  <=> r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_314])])).

fof(f785,plain,
    ( spl4_97
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_97])])).

fof(f99,plain,
    ( spl4_1
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f123,plain,
    ( spl4_7
  <=> v1_tsep_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f127,plain,
    ( spl4_8
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f131,plain,
    ( spl4_9
  <=> m1_pre_topc(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f204,plain,
    ( spl4_27
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f257,plain,
    ( spl4_35
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ v1_tsep_1(X2,X0)
        | ~ m1_pre_topc(X2,X0)
        | r1_tsep_1(X2,X1)
        | v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f907,plain,
    ( spl4_111
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_111])])).

fof(f1658,plain,
    ( spl4_202
  <=> ! [X7] :
        ( k1_tsep_1(sK3,X7,X7) = g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))
        | ~ m1_pre_topc(X7,sK3)
        | v2_struct_0(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_202])])).

fof(f1693,plain,
    ( spl4_206
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK3,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_206])])).

fof(f1713,plain,
    ( v1_tsep_1(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | spl4_1
    | spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_27
    | ~ spl4_35
    | ~ spl4_111
    | ~ spl4_202
    | ~ spl4_206 ),
    inference(backward_demodulation,[],[f1675,f1709])).

fof(f1709,plain,
    ( k1_tsep_1(sK0,sK1,sK1) = k1_tsep_1(sK3,sK1,sK1)
    | spl4_3
    | ~ spl4_12
    | ~ spl4_27
    | ~ spl4_206 ),
    inference(subsumption_resolution,[],[f1708,f108])).

fof(f1708,plain,
    ( k1_tsep_1(sK0,sK1,sK1) = k1_tsep_1(sK3,sK1,sK1)
    | v2_struct_0(sK1)
    | ~ spl4_12
    | ~ spl4_27
    | ~ spl4_206 ),
    inference(subsumption_resolution,[],[f1700,f144])).

fof(f1700,plain,
    ( k1_tsep_1(sK0,sK1,sK1) = k1_tsep_1(sK3,sK1,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ spl4_27
    | ~ spl4_206 ),
    inference(superposition,[],[f1694,f205])).

fof(f205,plain,
    ( ! [X0] :
        ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f204])).

fof(f1694,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK3,sK1,sK1)
    | ~ spl4_206 ),
    inference(avatar_component_clause,[],[f1693])).

fof(f1675,plain,
    ( v1_tsep_1(k1_tsep_1(sK3,sK1,sK1),k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | spl4_1
    | spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_35
    | ~ spl4_111
    | ~ spl4_202 ),
    inference(backward_demodulation,[],[f921,f1674])).

fof(f1674,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK3,sK1,sK1)
    | spl4_3
    | ~ spl4_9
    | ~ spl4_202 ),
    inference(subsumption_resolution,[],[f1671,f132])).

fof(f132,plain,
    ( m1_pre_topc(sK1,sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f131])).

fof(f1671,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK3,sK1,sK1)
    | spl4_3
    | ~ spl4_202 ),
    inference(resolution,[],[f1659,f108])).

fof(f1659,plain,
    ( ! [X7] :
        ( v2_struct_0(X7)
        | ~ m1_pre_topc(X7,sK3)
        | k1_tsep_1(sK3,X7,X7) = g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) )
    | ~ spl4_202 ),
    inference(avatar_component_clause,[],[f1658])).

fof(f921,plain,
    ( v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | spl4_1
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_35
    | ~ spl4_111 ),
    inference(subsumption_resolution,[],[f920,f112])).

fof(f920,plain,
    ( v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | spl4_1
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_35
    | ~ spl4_111 ),
    inference(subsumption_resolution,[],[f919,f128])).

fof(f128,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f919,plain,
    ( v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | spl4_1
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_35
    | ~ spl4_111 ),
    inference(subsumption_resolution,[],[f918,f124])).

fof(f124,plain,
    ( v1_tsep_1(sK3,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f918,plain,
    ( v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | spl4_1
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_35
    | ~ spl4_111 ),
    inference(subsumption_resolution,[],[f917,f100])).

fof(f100,plain,
    ( ~ v2_struct_0(sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f917,plain,
    ( v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK3)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_35
    | ~ spl4_111 ),
    inference(subsumption_resolution,[],[f916,f120])).

fof(f916,plain,
    ( v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK3)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ spl4_5
    | ~ spl4_35
    | ~ spl4_111 ),
    inference(subsumption_resolution,[],[f915,f116])).

fof(f915,plain,
    ( v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK3)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ spl4_35
    | ~ spl4_111 ),
    inference(superposition,[],[f258,f908])).

fof(f908,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_111 ),
    inference(avatar_component_clause,[],[f907])).

fof(f258,plain,
    ( ! [X2,X0,X1] :
        ( v1_tsep_1(k2_tsep_1(X0,X2,X1),X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ v1_tsep_1(X2,X0)
        | ~ m1_pre_topc(X2,X0)
        | r1_tsep_1(X2,X1)
        | v2_struct_0(X0) )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f257])).

fof(f3223,plain,
    ( ~ spl4_6
    | ~ spl4_12
    | ~ spl4_13
    | spl4_341 ),
    inference(avatar_contradiction_clause,[],[f3221])).

fof(f3221,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_13
    | spl4_341 ),
    inference(unit_resulting_resolution,[],[f120,f144,f3216,f148])).

fof(f3216,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_341 ),
    inference(avatar_component_clause,[],[f3215])).

fof(f2928,plain,
    ( spl4_294
    | spl4_1
    | spl4_2
    | spl4_3
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_60
    | ~ spl4_314 ),
    inference(avatar_split_clause,[],[f2884,f2848,f477,f143,f139,f127,f107,f103,f99,f2569])).

fof(f2569,plain,
    ( spl4_294
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_294])])).

fof(f477,plain,
    ( spl4_60
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | r1_tsep_1(X2,X0)
        | ~ r1_tsep_1(X2,k1_tsep_1(sK0,X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f2884,plain,
    ( r1_tsep_1(sK3,sK1)
    | spl4_1
    | spl4_2
    | spl4_3
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_60
    | ~ spl4_314 ),
    inference(subsumption_resolution,[],[f2883,f108])).

fof(f2883,plain,
    ( r1_tsep_1(sK3,sK1)
    | v2_struct_0(sK1)
    | spl4_1
    | spl4_2
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_60
    | ~ spl4_314 ),
    inference(subsumption_resolution,[],[f2882,f128])).

fof(f2882,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,sK1)
    | v2_struct_0(sK1)
    | spl4_1
    | spl4_2
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_60
    | ~ spl4_314 ),
    inference(subsumption_resolution,[],[f2881,f100])).

fof(f2881,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,sK1)
    | v2_struct_0(sK1)
    | spl4_2
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_60
    | ~ spl4_314 ),
    inference(subsumption_resolution,[],[f2880,f140])).

fof(f2880,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,sK1)
    | v2_struct_0(sK1)
    | spl4_2
    | ~ spl4_12
    | ~ spl4_60
    | ~ spl4_314 ),
    inference(subsumption_resolution,[],[f2879,f104])).

fof(f2879,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,sK1)
    | v2_struct_0(sK1)
    | ~ spl4_12
    | ~ spl4_60
    | ~ spl4_314 ),
    inference(subsumption_resolution,[],[f2870,f144])).

fof(f2870,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,sK1)
    | v2_struct_0(sK1)
    | ~ spl4_60
    | ~ spl4_314 ),
    inference(resolution,[],[f2849,f478])).

fof(f478,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tsep_1(X2,k1_tsep_1(sK0,X0,X1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | r1_tsep_1(X2,X0)
        | v2_struct_0(X0) )
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f477])).

fof(f2849,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_314 ),
    inference(avatar_component_clause,[],[f2848])).

fof(f2867,plain,
    ( spl4_2
    | spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_19
    | ~ spl4_97 ),
    inference(avatar_contradiction_clause,[],[f2866])).

fof(f2866,plain,
    ( $false
    | spl4_2
    | spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_19
    | ~ spl4_97 ),
    inference(subsumption_resolution,[],[f2865,f112])).

fof(f2865,plain,
    ( v2_struct_0(sK0)
    | spl4_2
    | spl4_3
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_19
    | ~ spl4_97 ),
    inference(subsumption_resolution,[],[f2864,f140])).

fof(f2864,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl4_2
    | spl4_3
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_19
    | ~ spl4_97 ),
    inference(subsumption_resolution,[],[f2863,f104])).

fof(f2863,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_19
    | ~ spl4_97 ),
    inference(subsumption_resolution,[],[f2862,f144])).

fof(f2862,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_19
    | ~ spl4_97 ),
    inference(subsumption_resolution,[],[f2861,f108])).

fof(f2861,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl4_6
    | ~ spl4_19
    | ~ spl4_97 ),
    inference(subsumption_resolution,[],[f2859,f120])).

fof(f2859,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl4_19
    | ~ spl4_97 ),
    inference(resolution,[],[f786,f169])).

fof(f169,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl4_19
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f786,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_97 ),
    inference(avatar_component_clause,[],[f785])).

fof(f2853,plain,
    ( ~ spl4_98
    | spl4_314
    | spl4_97
    | spl4_315
    | spl4_3
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_27
    | ~ spl4_61
    | ~ spl4_111
    | ~ spl4_202
    | ~ spl4_206 ),
    inference(avatar_split_clause,[],[f1712,f1693,f1658,f907,f484,f204,f143,f131,f107,f2851,f785,f2848,f788])).

fof(f484,plain,
    ( spl4_61
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(sK3,X0)
        | m1_pre_topc(k2_tsep_1(sK0,sK3,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f1712,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | spl4_3
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_27
    | ~ spl4_61
    | ~ spl4_111
    | ~ spl4_202
    | ~ spl4_206 ),
    inference(backward_demodulation,[],[f1676,f1709])).

fof(f1676,plain,
    ( m1_pre_topc(k1_tsep_1(sK3,sK1,sK1),k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | spl4_3
    | ~ spl4_9
    | ~ spl4_61
    | ~ spl4_111
    | ~ spl4_202 ),
    inference(backward_demodulation,[],[f914,f1674])).

fof(f914,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl4_61
    | ~ spl4_111 ),
    inference(superposition,[],[f485,f908])).

fof(f485,plain,
    ( ! [X0] :
        ( m1_pre_topc(k2_tsep_1(sK0,sK3,X0),X0)
        | v2_struct_0(X0)
        | r1_tsep_1(sK3,X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f484])).

fof(f2588,plain,
    ( spl4_1
    | spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_26
    | ~ spl4_294 ),
    inference(avatar_contradiction_clause,[],[f2578])).

fof(f2578,plain,
    ( $false
    | spl4_1
    | spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_26
    | ~ spl4_294 ),
    inference(unit_resulting_resolution,[],[f112,f116,f120,f100,f128,f144,f108,f132,f2570,f197])).

fof(f197,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tsep_1(X2,X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X0) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl4_26
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_pre_topc(X1,X2)
        | ~ r1_tsep_1(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f2570,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl4_294 ),
    inference(avatar_component_clause,[],[f2569])).

fof(f1695,plain,
    ( spl4_206
    | spl4_3
    | ~ spl4_9
    | ~ spl4_202 ),
    inference(avatar_split_clause,[],[f1674,f1658,f131,f107,f1693])).

fof(f1660,plain,
    ( spl4_202
    | spl4_1
    | ~ spl4_8
    | ~ spl4_195 ),
    inference(avatar_split_clause,[],[f1612,f1593,f127,f99,f1658])).

fof(f1593,plain,
    ( spl4_195
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,X1)
        | k1_tsep_1(X1,X0,X0) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_195])])).

fof(f1612,plain,
    ( ! [X7] :
        ( k1_tsep_1(sK3,X7,X7) = g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))
        | ~ m1_pre_topc(X7,sK3)
        | v2_struct_0(X7) )
    | spl4_1
    | ~ spl4_8
    | ~ spl4_195 ),
    inference(subsumption_resolution,[],[f1608,f128])).

fof(f1608,plain,
    ( ! [X7] :
        ( k1_tsep_1(sK3,X7,X7) = g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))
        | ~ m1_pre_topc(sK3,sK0)
        | ~ m1_pre_topc(X7,sK3)
        | v2_struct_0(X7) )
    | spl4_1
    | ~ spl4_195 ),
    inference(resolution,[],[f1594,f100])).

fof(f1594,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X1)
        | k1_tsep_1(X1,X0,X0) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0) )
    | ~ spl4_195 ),
    inference(avatar_component_clause,[],[f1593])).

fof(f1595,plain,
    ( spl4_195
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_173 ),
    inference(avatar_split_clause,[],[f1332,f1319,f119,f115,f1593])).

fof(f1319,plain,
    ( spl4_173
  <=> ! [X1,X3,X2] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X2)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X2,X1,X1)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ v2_pre_topc(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_173])])).

fof(f1332,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | k1_tsep_1(X1,X0,X0) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0) )
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_173 ),
    inference(subsumption_resolution,[],[f1331,f116])).

fof(f1331,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | k1_tsep_1(X1,X0,X0) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_6
    | ~ spl4_173 ),
    inference(duplicate_literal_removal,[],[f1329])).

fof(f1329,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | k1_tsep_1(X1,X0,X0) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_6
    | ~ spl4_173 ),
    inference(resolution,[],[f1320,f120])).

fof(f1320,plain,
    ( ! [X2,X3,X1] :
        ( ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(X1,X2)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X2,X1,X1)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_173 ),
    inference(avatar_component_clause,[],[f1319])).

fof(f1321,plain,
    ( spl4_173
    | ~ spl4_18
    | ~ spl4_99 ),
    inference(avatar_split_clause,[],[f796,f792,f164,f1319])).

fof(f792,plain,
    ( spl4_99
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).

fof(f796,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X2)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X2,X1,X1)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_18
    | ~ spl4_99 ),
    inference(resolution,[],[f793,f165])).

fof(f793,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl4_99 ),
    inference(avatar_component_clause,[],[f792])).

fof(f913,plain,
    ( spl4_112
    | ~ spl4_27
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f250,f239,f204,f911])).

fof(f239,plain,
    ( spl4_31
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
        | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
        | v1_tsep_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f250,plain,
    ( ! [X0,X1] :
        ( ~ v1_tsep_1(k1_tsep_1(sK0,X0,X0),X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X0),X1)
        | v1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl4_27
    | ~ spl4_31 ),
    inference(superposition,[],[f240,f205])).

fof(f240,plain,
    ( ! [X0,X1] :
        ( ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
        | v1_tsep_1(X1,X0) )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f239])).

fof(f909,plain,
    ( spl4_111
    | spl4_3
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_109 ),
    inference(avatar_split_clause,[],[f891,f882,f143,f131,f107,f907])).

fof(f882,plain,
    ( spl4_109
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,X0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_109])])).

fof(f891,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2))
    | spl4_3
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_109 ),
    inference(subsumption_resolution,[],[f890,f132])).

fof(f890,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2))
    | spl4_3
    | ~ spl4_12
    | ~ spl4_109 ),
    inference(subsumption_resolution,[],[f887,f144])).

fof(f887,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2))
    | spl4_3
    | ~ spl4_109 ),
    inference(resolution,[],[f883,f108])).

fof(f883,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,X0,sK2)) )
    | ~ spl4_109 ),
    inference(avatar_component_clause,[],[f882])).

fof(f884,plain,
    ( spl4_109
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_73 ),
    inference(avatar_split_clause,[],[f624,f612,f139,f127,f119,f115,f111,f882])).

fof(f612,plain,
    ( spl4_73
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(X0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,sK3,k1_tsep_1(X0,X1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f624,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,X0,sK2)) )
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_73 ),
    inference(subsumption_resolution,[],[f623,f112])).

fof(f623,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,X0,sK2)) )
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_73 ),
    inference(subsumption_resolution,[],[f622,f140])).

fof(f622,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,X0,sK2)) )
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_73 ),
    inference(subsumption_resolution,[],[f621,f128])).

fof(f621,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,X0,sK2)) )
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_73 ),
    inference(subsumption_resolution,[],[f619,f116])).

fof(f619,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,X0,sK2)) )
    | ~ spl4_6
    | ~ spl4_73 ),
    inference(resolution,[],[f613,f120])).

fof(f613,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(X0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,sK3,k1_tsep_1(X0,X1,sK2)) )
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f612])).

fof(f808,plain,
    ( spl4_2
    | spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_21
    | spl4_98 ),
    inference(avatar_contradiction_clause,[],[f807])).

fof(f807,plain,
    ( $false
    | spl4_2
    | spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_21
    | spl4_98 ),
    inference(subsumption_resolution,[],[f806,f112])).

fof(f806,plain,
    ( v2_struct_0(sK0)
    | spl4_2
    | spl4_3
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_21
    | spl4_98 ),
    inference(subsumption_resolution,[],[f805,f140])).

fof(f805,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl4_2
    | spl4_3
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_21
    | spl4_98 ),
    inference(subsumption_resolution,[],[f804,f104])).

fof(f804,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_21
    | spl4_98 ),
    inference(subsumption_resolution,[],[f803,f144])).

fof(f803,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_21
    | spl4_98 ),
    inference(subsumption_resolution,[],[f802,f108])).

fof(f802,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl4_6
    | ~ spl4_21
    | spl4_98 ),
    inference(subsumption_resolution,[],[f800,f120])).

fof(f800,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl4_21
    | spl4_98 ),
    inference(resolution,[],[f789,f177])).

fof(f177,plain,
    ( ! [X2,X0,X1] :
        ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl4_21
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f789,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | spl4_98 ),
    inference(avatar_component_clause,[],[f788])).

fof(f794,plain,
    ( spl4_99
    | ~ spl4_6
    | ~ spl4_77 ),
    inference(avatar_split_clause,[],[f650,f640,f119,f792])).

fof(f640,plain,
    ( spl4_77
  <=> ! [X1,X3,X2] :
        ( ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X1,X2,X2)
        | ~ m1_pre_topc(X1,X3)
        | ~ l1_pre_topc(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f650,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_6
    | ~ spl4_77 ),
    inference(resolution,[],[f641,f120])).

fof(f641,plain,
    ( ! [X2,X3,X1] :
        ( ~ l1_pre_topc(X3)
        | v2_struct_0(X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X1,X2,X2)
        | ~ m1_pre_topc(X1,X3)
        | ~ v2_pre_topc(X1) )
    | ~ spl4_77 ),
    inference(avatar_component_clause,[],[f640])).

fof(f642,plain,
    ( spl4_77
    | ~ spl4_13
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f200,f180,f147,f640])).

fof(f180,plain,
    ( spl4_22
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f200,plain,
    ( ! [X2,X3,X1] :
        ( ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X1,X2,X2)
        | ~ m1_pre_topc(X1,X3)
        | ~ l1_pre_topc(X3) )
    | ~ spl4_13
    | ~ spl4_22 ),
    inference(resolution,[],[f181,f148])).

fof(f181,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f180])).

fof(f614,plain,
    ( spl4_73
    | spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f463,f438,f135,f103,f99,f612])).

fof(f135,plain,
    ( spl4_10
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f438,plain,
    ( spl4_56
  <=> ! [X1,X3,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | ~ m1_pre_topc(X1,X2)
        | ~ r1_tsep_1(X2,X3)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f463,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(X0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,sK3,k1_tsep_1(X0,X1,sK2)) )
    | spl4_1
    | spl4_2
    | ~ spl4_10
    | ~ spl4_56 ),
    inference(subsumption_resolution,[],[f462,f104])).

fof(f462,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(X0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,sK3,k1_tsep_1(X0,X1,sK2)) )
    | spl4_1
    | ~ spl4_10
    | ~ spl4_56 ),
    inference(subsumption_resolution,[],[f461,f100])).

fof(f461,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(X0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,sK3,k1_tsep_1(X0,X1,sK2)) )
    | ~ spl4_10
    | ~ spl4_56 ),
    inference(resolution,[],[f439,f136])).

fof(f136,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f135])).

fof(f439,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tsep_1(X2,X3)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X0)
        | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f438])).

fof(f486,plain,
    ( spl4_61
    | spl4_1
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f474,f465,f127,f123,f99,f484])).

fof(f465,plain,
    ( spl4_59
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ v1_tsep_1(X1,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | r1_tsep_1(X1,X0)
        | m1_pre_topc(k2_tsep_1(sK0,X1,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f474,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(sK3,X0)
        | m1_pre_topc(k2_tsep_1(sK0,sK3,X0),X0) )
    | spl4_1
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_59 ),
    inference(subsumption_resolution,[],[f473,f128])).

fof(f473,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,sK0)
        | r1_tsep_1(sK3,X0)
        | m1_pre_topc(k2_tsep_1(sK0,sK3,X0),X0) )
    | spl4_1
    | ~ spl4_7
    | ~ spl4_59 ),
    inference(subsumption_resolution,[],[f471,f100])).

fof(f471,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK3)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,sK0)
        | r1_tsep_1(sK3,X0)
        | m1_pre_topc(k2_tsep_1(sK0,sK3,X0),X0) )
    | ~ spl4_7
    | ~ spl4_59 ),
    inference(resolution,[],[f466,f124])).

fof(f466,plain,
    ( ! [X0,X1] :
        ( ~ v1_tsep_1(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | r1_tsep_1(X1,X0)
        | m1_pre_topc(k2_tsep_1(sK0,X1,X0),X0) )
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f465])).

fof(f479,plain,
    ( spl4_60
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f359,f317,f119,f115,f111,f477])).

fof(f317,plain,
    ( spl4_41
  <=> ! [X1,X3,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | r1_tsep_1(X3,X1)
        | ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f359,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | r1_tsep_1(X2,X0)
        | ~ r1_tsep_1(X2,k1_tsep_1(sK0,X0,X1)) )
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f358,f112])).

fof(f358,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | r1_tsep_1(X2,X0)
        | ~ r1_tsep_1(X2,k1_tsep_1(sK0,X0,X1)) )
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f356,f116])).

fof(f356,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | r1_tsep_1(X2,X0)
        | ~ r1_tsep_1(X2,k1_tsep_1(sK0,X0,X1)) )
    | ~ spl4_6
    | ~ spl4_41 ),
    inference(resolution,[],[f318,f120])).

fof(f318,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | r1_tsep_1(X3,X1)
        | ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f317])).

fof(f467,plain,
    ( spl4_59
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f303,f270,f119,f115,f111,f465])).

fof(f270,plain,
    ( spl4_36
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ v1_tsep_1(X2,X0)
        | ~ m1_pre_topc(X2,X0)
        | r1_tsep_1(X2,X1)
        | m1_pre_topc(k2_tsep_1(X0,X2,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f303,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ v1_tsep_1(X1,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | r1_tsep_1(X1,X0)
        | m1_pre_topc(k2_tsep_1(sK0,X1,X0),X0) )
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f302,f112])).

fof(f302,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ v1_tsep_1(X1,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | r1_tsep_1(X1,X0)
        | m1_pre_topc(k2_tsep_1(sK0,X1,X0),X0) )
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f300,f116])).

fof(f300,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ v1_tsep_1(X1,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | r1_tsep_1(X1,X0)
        | m1_pre_topc(k2_tsep_1(sK0,X1,X0),X0) )
    | ~ spl4_6
    | ~ spl4_36 ),
    inference(resolution,[],[f271,f120])).

fof(f271,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ v1_tsep_1(X2,X0)
        | ~ m1_pre_topc(X2,X0)
        | r1_tsep_1(X2,X1)
        | m1_pre_topc(k2_tsep_1(X0,X2,X1),X1) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f270])).

fof(f440,plain,(
    spl4_56 ),
    inference(avatar_split_clause,[],[f71,f438])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ r1_tsep_1(X2,X3)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
                        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tmap_1)).

fof(f319,plain,(
    spl4_41 ),
    inference(avatar_split_clause,[],[f63,f317])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | r1_tsep_1(X3,X1)
      | ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      | ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) ) )
                    & ( ~ r1_tsep_1(X3,X2)
                      | ~ r1_tsep_1(X3,X1)
                      | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      | ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) ) )
                    & ( ~ r1_tsep_1(X2,X3)
                      | ~ r1_tsep_1(X1,X3)
                      | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      | ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) ) )
                    & ( ~ r1_tsep_1(X3,X2)
                      | ~ r1_tsep_1(X3,X1)
                      | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      | ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) ) )
                    & ( ~ r1_tsep_1(X2,X3)
                      | ~ r1_tsep_1(X1,X3)
                      | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                        & ~ ( r1_tsep_1(X3,X2)
                            & r1_tsep_1(X3,X1) ) )
                    & ~ ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1)
                        & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ~ ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                        & ~ ( r1_tsep_1(X2,X3)
                            & r1_tsep_1(X1,X3) ) )
                    & ~ ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3)
                        & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tmap_1)).

fof(f295,plain,
    ( ~ spl4_16
    | spl4_2
    | ~ spl4_11
    | spl4_14
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f292,f278,f151,f139,f103,f157])).

fof(f157,plain,
    ( spl4_16
  <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f151,plain,
    ( spl4_14
  <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f292,plain,
    ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | spl4_2
    | ~ spl4_11
    | spl4_14
    | ~ spl4_38 ),
    inference(backward_demodulation,[],[f152,f291])).

fof(f152,plain,
    ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f280,plain,
    ( spl4_38
    | spl4_3
    | ~ spl4_12
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f266,f253,f143,f107,f278])).

fof(f253,plain,
    ( spl4_34
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f266,plain,
    ( ! [X3] :
        ( v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | k1_tsep_1(sK0,sK1,X3) = k1_tsep_1(sK0,X3,sK1) )
    | spl4_3
    | ~ spl4_12
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f261,f108])).

fof(f261,plain,
    ( ! [X3] :
        ( v2_struct_0(sK1)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | k1_tsep_1(sK0,sK1,X3) = k1_tsep_1(sK0,X3,sK1) )
    | ~ spl4_12
    | ~ spl4_34 ),
    inference(resolution,[],[f254,f144])).

fof(f254,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0) )
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f253])).

fof(f272,plain,(
    spl4_36 ),
    inference(avatar_split_clause,[],[f59,f270])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ v1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X2,X1)
      | m1_pre_topc(k2_tsep_1(X0,X2,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                & v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) )
              | r1_tsep_1(X2,X1)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                & v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) )
              | r1_tsep_1(X2,X1)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X2,X1)
               => ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                  & v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tmap_1)).

fof(f259,plain,(
    spl4_35 ),
    inference(avatar_split_clause,[],[f58,f257])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ v1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X2,X1)
      | v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f255,plain,
    ( spl4_34
    | spl4_4
    | ~ spl4_6
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f237,f208,f119,f111,f253])).

fof(f208,plain,
    ( spl4_28
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f237,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0) )
    | spl4_4
    | ~ spl4_6
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f235,f112])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0) )
    | ~ spl4_6
    | ~ spl4_28 ),
    inference(resolution,[],[f209,f120])).

fof(f209,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f208])).

fof(f241,plain,(
    spl4_31 ),
    inference(avatar_split_clause,[],[f95,f239])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f94,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f88,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
      | ~ v1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tmap_1)).

fof(f221,plain,
    ( spl4_2
    | spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | spl4_16
    | ~ spl4_24 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | spl4_2
    | spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | spl4_16
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f219,f112])).

fof(f219,plain,
    ( v2_struct_0(sK0)
    | spl4_2
    | spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | spl4_16
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f218,f140])).

fof(f218,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl4_2
    | spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_12
    | spl4_16
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f217,f104])).

fof(f217,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_12
    | spl4_16
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f216,f144])).

fof(f216,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | spl4_16
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f215,f108])).

fof(f215,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl4_5
    | ~ spl4_6
    | spl4_16
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f214,f120])).

fof(f214,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl4_5
    | spl4_16
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f212,f116])).

fof(f212,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl4_16
    | ~ spl4_24 ),
    inference(resolution,[],[f189,f158])).

fof(f158,plain,
    ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f157])).

fof(f189,plain,
    ( ! [X2,X0,X1] :
        ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl4_24
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f210,plain,(
    spl4_28 ),
    inference(avatar_split_clause,[],[f79,f208])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(f206,plain,
    ( spl4_27
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f202,f180,f119,f115,f111,f204])).

fof(f202,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) )
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f201,f112])).

fof(f201,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) )
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f199,f116])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) )
    | ~ spl4_6
    | ~ spl4_22 ),
    inference(resolution,[],[f181,f120])).

fof(f198,plain,(
    spl4_26 ),
    inference(avatar_split_clause,[],[f62,f196])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ r1_tsep_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f190,plain,(
    spl4_24 ),
    inference(avatar_split_clause,[],[f60,f188])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f186,plain,(
    spl4_23 ),
    inference(avatar_split_clause,[],[f85,f184])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_pre_topc(k1_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tmap_1)).

fof(f182,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f57,f180])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
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
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f178,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f82,f176])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f170,plain,(
    spl4_19 ),
    inference(avatar_split_clause,[],[f80,f168])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f166,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f74,f164])).

fof(f162,plain,
    ( ~ spl4_14
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f43,f160,f157,f154,f151])).

fof(f43,plain,
    ( ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                    | ~ v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                    | ~ v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                    | ~ v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                    | ~ v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
                      & v1_tsep_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( r1_tsep_1(X3,X2)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                        & v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                        & m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                        & v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( r1_tsep_1(X3,X2)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                      & v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                      & m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                      & v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tmap_1)).

fof(f149,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f56,f147])).

fof(f145,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f52,f143])).

fof(f52,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f141,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f50,f139])).

fof(f50,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f137,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f48,f135])).

fof(f48,plain,(
    r1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f133,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f47,f131])).

fof(f47,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f129,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f46,f127])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f125,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f45,f123])).

fof(f45,plain,(
    v1_tsep_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f121,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f55,f119])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f117,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f54,f115])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f113,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f53,f111])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f109,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f51,f107])).

fof(f51,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f105,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f49,f103])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f101,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f44,f99])).

fof(f44,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:37 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.20/0.47  % (12335)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (12327)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (12336)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (12333)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (12323)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (12328)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (12326)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (12325)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (12331)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (12332)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (12320)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (12334)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (12321)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (12321)Refutation not found, incomplete strategy% (12321)------------------------------
% 0.20/0.50  % (12321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (12321)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (12321)Memory used [KB]: 10618
% 0.20/0.50  % (12321)Time elapsed: 0.082 s
% 0.20/0.50  % (12321)------------------------------
% 0.20/0.50  % (12321)------------------------------
% 0.20/0.50  % (12340)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (12337)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (12341)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (12329)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (12338)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (12324)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (12322)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (12330)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  % (12341)Refutation not found, incomplete strategy% (12341)------------------------------
% 0.20/0.52  % (12341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12341)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12341)Memory used [KB]: 10618
% 0.20/0.52  % (12341)Time elapsed: 0.120 s
% 0.20/0.52  % (12341)------------------------------
% 0.20/0.52  % (12341)------------------------------
% 2.29/0.68  % (12320)Refutation not found, incomplete strategy% (12320)------------------------------
% 2.29/0.68  % (12320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.68  % (12320)Termination reason: Refutation not found, incomplete strategy
% 2.29/0.68  
% 2.29/0.68  % (12320)Memory used [KB]: 7931
% 2.29/0.68  % (12320)Time elapsed: 0.268 s
% 2.29/0.68  % (12320)------------------------------
% 2.29/0.68  % (12320)------------------------------
% 4.12/0.91  % (12332)Time limit reached!
% 4.12/0.91  % (12332)------------------------------
% 4.12/0.91  % (12332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/0.91  % (12325)Time limit reached!
% 4.12/0.91  % (12325)------------------------------
% 4.12/0.91  % (12325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/0.91  % (12325)Termination reason: Time limit
% 4.12/0.91  
% 4.12/0.91  % (12325)Memory used [KB]: 9338
% 4.12/0.91  % (12325)Time elapsed: 0.503 s
% 4.12/0.91  % (12325)------------------------------
% 4.12/0.91  % (12325)------------------------------
% 4.12/0.92  % (12330)Time limit reached!
% 4.12/0.92  % (12330)------------------------------
% 4.12/0.92  % (12330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/0.92  % (12330)Termination reason: Time limit
% 4.12/0.92  % (12330)Termination phase: Saturation
% 4.12/0.92  
% 4.12/0.92  % (12330)Memory used [KB]: 13048
% 4.12/0.92  % (12330)Time elapsed: 0.517 s
% 4.12/0.92  % (12330)------------------------------
% 4.12/0.92  % (12330)------------------------------
% 4.12/0.92  % (12332)Termination reason: Time limit
% 4.12/0.92  % (12332)Termination phase: Saturation
% 4.12/0.92  
% 4.12/0.92  % (12332)Memory used [KB]: 12153
% 4.12/0.92  % (12332)Time elapsed: 0.500 s
% 4.12/0.92  % (12332)------------------------------
% 4.12/0.92  % (12332)------------------------------
% 4.70/0.95  % (12329)Refutation found. Thanks to Tanya!
% 4.70/0.95  % SZS status Theorem for theBenchmark
% 4.70/0.95  % SZS output start Proof for theBenchmark
% 4.70/0.95  fof(f3389,plain,(
% 4.70/0.95    $false),
% 4.70/0.95    inference(avatar_sat_refutation,[],[f101,f105,f109,f113,f117,f121,f125,f129,f133,f137,f141,f145,f149,f162,f166,f170,f178,f182,f186,f190,f198,f206,f210,f221,f241,f255,f259,f272,f280,f295,f319,f440,f467,f479,f486,f614,f642,f794,f808,f884,f909,f913,f1321,f1595,f1660,f1695,f2588,f2853,f2867,f2928,f3223,f3281,f3303,f3310,f3330,f3375,f3378,f3388])).
% 4.70/0.95  fof(f3388,plain,(
% 4.70/0.95    ~spl4_98 | ~spl4_6 | ~spl4_354),
% 4.70/0.95    inference(avatar_split_clause,[],[f3384,f3373,f119,f788])).
% 4.70/0.95  fof(f788,plain,(
% 4.70/0.95    spl4_98 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).
% 4.70/0.95  fof(f119,plain,(
% 4.70/0.95    spl4_6 <=> l1_pre_topc(sK0)),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 4.70/0.95  fof(f3373,plain,(
% 4.70/0.95    spl4_354 <=> ! [X0] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0) | ~l1_pre_topc(X0))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_354])])).
% 4.70/0.95  fof(f3384,plain,(
% 4.70/0.95    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | (~spl4_6 | ~spl4_354)),
% 4.70/0.95    inference(resolution,[],[f3374,f120])).
% 4.70/0.95  fof(f120,plain,(
% 4.70/0.95    l1_pre_topc(sK0) | ~spl4_6),
% 4.70/0.95    inference(avatar_component_clause,[],[f119])).
% 4.70/0.95  fof(f3374,plain,(
% 4.70/0.95    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0)) ) | ~spl4_354),
% 4.70/0.95    inference(avatar_component_clause,[],[f3373])).
% 4.70/0.95  fof(f3378,plain,(
% 4.70/0.95    ~spl4_17 | spl4_2 | ~spl4_11 | spl4_15 | ~spl4_38),
% 4.70/0.95    inference(avatar_split_clause,[],[f293,f278,f154,f139,f103,f160])).
% 4.70/0.95  fof(f160,plain,(
% 4.70/0.95    spl4_17 <=> v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 4.70/0.95  fof(f103,plain,(
% 4.70/0.95    spl4_2 <=> v2_struct_0(sK2)),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 4.70/0.95  fof(f139,plain,(
% 4.70/0.95    spl4_11 <=> m1_pre_topc(sK2,sK0)),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 4.70/0.95  fof(f154,plain,(
% 4.70/0.95    spl4_15 <=> v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 4.70/0.95  fof(f278,plain,(
% 4.70/0.95    spl4_38 <=> ! [X3] : (v2_struct_0(X3) | ~m1_pre_topc(X3,sK0) | k1_tsep_1(sK0,sK1,X3) = k1_tsep_1(sK0,X3,sK1))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 4.70/0.95  fof(f293,plain,(
% 4.70/0.95    ~v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) | (spl4_2 | ~spl4_11 | spl4_15 | ~spl4_38)),
% 4.70/0.95    inference(backward_demodulation,[],[f155,f291])).
% 4.70/0.95  fof(f291,plain,(
% 4.70/0.95    k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1) | (spl4_2 | ~spl4_11 | ~spl4_38)),
% 4.70/0.95    inference(subsumption_resolution,[],[f287,f104])).
% 4.70/0.95  fof(f104,plain,(
% 4.70/0.95    ~v2_struct_0(sK2) | spl4_2),
% 4.70/0.95    inference(avatar_component_clause,[],[f103])).
% 4.70/0.95  fof(f287,plain,(
% 4.70/0.95    v2_struct_0(sK2) | k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1) | (~spl4_11 | ~spl4_38)),
% 4.70/0.95    inference(resolution,[],[f279,f140])).
% 4.70/0.95  fof(f140,plain,(
% 4.70/0.95    m1_pre_topc(sK2,sK0) | ~spl4_11),
% 4.70/0.95    inference(avatar_component_clause,[],[f139])).
% 4.70/0.95  fof(f279,plain,(
% 4.70/0.95    ( ! [X3] : (~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | k1_tsep_1(sK0,sK1,X3) = k1_tsep_1(sK0,X3,sK1)) ) | ~spl4_38),
% 4.70/0.95    inference(avatar_component_clause,[],[f278])).
% 4.70/0.95  fof(f155,plain,(
% 4.70/0.95    ~v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1)) | spl4_15),
% 4.70/0.95    inference(avatar_component_clause,[],[f154])).
% 4.70/0.95  fof(f3375,plain,(
% 4.70/0.95    spl4_354 | ~spl4_13 | spl4_350),
% 4.70/0.95    inference(avatar_split_clause,[],[f3346,f3301,f147,f3373])).
% 4.70/0.95  fof(f147,plain,(
% 4.70/0.95    spl4_13 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 4.70/0.95  fof(f3301,plain,(
% 4.70/0.95    spl4_350 <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_350])])).
% 4.70/0.95  fof(f3346,plain,(
% 4.70/0.95    ( ! [X0] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0) | ~l1_pre_topc(X0)) ) | (~spl4_13 | spl4_350)),
% 4.70/0.95    inference(resolution,[],[f3302,f148])).
% 4.70/0.95  fof(f148,plain,(
% 4.70/0.95    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl4_13),
% 4.70/0.95    inference(avatar_component_clause,[],[f147])).
% 4.70/0.95  fof(f3302,plain,(
% 4.70/0.95    ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | spl4_350),
% 4.70/0.95    inference(avatar_component_clause,[],[f3301])).
% 4.70/0.95  fof(f3330,plain,(
% 4.70/0.95    spl4_2 | spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_11 | ~spl4_12 | ~spl4_23 | spl4_348),
% 4.70/0.95    inference(avatar_contradiction_clause,[],[f3329])).
% 4.70/0.95  fof(f3329,plain,(
% 4.70/0.95    $false | (spl4_2 | spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_11 | ~spl4_12 | ~spl4_23 | spl4_348)),
% 4.70/0.95    inference(subsumption_resolution,[],[f3328,f112])).
% 4.70/0.95  fof(f112,plain,(
% 4.70/0.95    ~v2_struct_0(sK0) | spl4_4),
% 4.70/0.95    inference(avatar_component_clause,[],[f111])).
% 4.70/0.95  fof(f111,plain,(
% 4.70/0.95    spl4_4 <=> v2_struct_0(sK0)),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 4.70/0.95  fof(f3328,plain,(
% 4.70/0.95    v2_struct_0(sK0) | (spl4_2 | spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_11 | ~spl4_12 | ~spl4_23 | spl4_348)),
% 4.70/0.95    inference(subsumption_resolution,[],[f3327,f140])).
% 4.70/0.95  fof(f3327,plain,(
% 4.70/0.95    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl4_2 | spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_12 | ~spl4_23 | spl4_348)),
% 4.70/0.95    inference(subsumption_resolution,[],[f3326,f104])).
% 4.70/0.95  fof(f3326,plain,(
% 4.70/0.95    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_12 | ~spl4_23 | spl4_348)),
% 4.70/0.95    inference(subsumption_resolution,[],[f3325,f144])).
% 4.70/0.95  fof(f144,plain,(
% 4.70/0.95    m1_pre_topc(sK1,sK0) | ~spl4_12),
% 4.70/0.95    inference(avatar_component_clause,[],[f143])).
% 4.70/0.95  fof(f143,plain,(
% 4.70/0.95    spl4_12 <=> m1_pre_topc(sK1,sK0)),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 4.70/0.95  fof(f3325,plain,(
% 4.70/0.95    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_23 | spl4_348)),
% 4.70/0.95    inference(subsumption_resolution,[],[f3324,f108])).
% 4.70/0.95  fof(f108,plain,(
% 4.70/0.95    ~v2_struct_0(sK1) | spl4_3),
% 4.70/0.95    inference(avatar_component_clause,[],[f107])).
% 4.70/0.95  fof(f107,plain,(
% 4.70/0.95    spl4_3 <=> v2_struct_0(sK1)),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 4.70/0.95  fof(f3324,plain,(
% 4.70/0.95    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl4_5 | ~spl4_6 | ~spl4_23 | spl4_348)),
% 4.70/0.95    inference(subsumption_resolution,[],[f3323,f120])).
% 4.70/0.95  fof(f3323,plain,(
% 4.70/0.95    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl4_5 | ~spl4_23 | spl4_348)),
% 4.70/0.95    inference(subsumption_resolution,[],[f3320,f116])).
% 4.70/0.95  fof(f116,plain,(
% 4.70/0.95    v2_pre_topc(sK0) | ~spl4_5),
% 4.70/0.95    inference(avatar_component_clause,[],[f115])).
% 4.70/0.95  fof(f115,plain,(
% 4.70/0.95    spl4_5 <=> v2_pre_topc(sK0)),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 4.70/0.95  fof(f3320,plain,(
% 4.70/0.95    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl4_23 | spl4_348)),
% 4.70/0.95    inference(resolution,[],[f3296,f185])).
% 4.70/0.95  fof(f185,plain,(
% 4.70/0.95    ( ! [X2,X0,X1] : (v2_pre_topc(k1_tsep_1(X0,X1,X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) ) | ~spl4_23),
% 4.70/0.95    inference(avatar_component_clause,[],[f184])).
% 4.70/0.95  fof(f184,plain,(
% 4.70/0.95    spl4_23 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_pre_topc(k1_tsep_1(X0,X1,X2)))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 4.70/0.95  fof(f3296,plain,(
% 4.70/0.95    ~v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | spl4_348),
% 4.70/0.95    inference(avatar_component_clause,[],[f3295])).
% 4.70/0.95  fof(f3295,plain,(
% 4.70/0.95    spl4_348 <=> v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_348])])).
% 4.70/0.95  fof(f3310,plain,(
% 4.70/0.95    ~spl4_5 | ~spl4_6 | ~spl4_12 | ~spl4_18 | spl4_349),
% 4.70/0.95    inference(avatar_contradiction_clause,[],[f3308])).
% 4.70/0.95  fof(f3308,plain,(
% 4.70/0.95    $false | (~spl4_5 | ~spl4_6 | ~spl4_12 | ~spl4_18 | spl4_349)),
% 4.70/0.95    inference(unit_resulting_resolution,[],[f116,f120,f144,f3299,f165])).
% 4.70/0.95  fof(f165,plain,(
% 4.70/0.95    ( ! [X0,X1] : (v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0)) ) | ~spl4_18),
% 4.70/0.95    inference(avatar_component_clause,[],[f164])).
% 4.70/0.95  fof(f164,plain,(
% 4.70/0.95    spl4_18 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 4.70/0.95  fof(f3299,plain,(
% 4.70/0.95    ~v2_pre_topc(sK1) | spl4_349),
% 4.70/0.95    inference(avatar_component_clause,[],[f3298])).
% 4.70/0.95  fof(f3298,plain,(
% 4.70/0.95    spl4_349 <=> v2_pre_topc(sK1)),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_349])])).
% 4.70/0.95  fof(f3303,plain,(
% 4.70/0.95    ~spl4_348 | ~spl4_341 | ~spl4_349 | ~spl4_350 | spl4_3 | ~spl4_12 | spl4_17 | ~spl4_112 | ~spl4_315 | ~spl4_347),
% 4.70/0.95    inference(avatar_split_clause,[],[f3291,f3279,f2851,f911,f160,f143,f107,f3301,f3298,f3215,f3295])).
% 4.70/0.95  fof(f3215,plain,(
% 4.70/0.95    spl4_341 <=> l1_pre_topc(sK1)),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_341])])).
% 4.70/0.95  fof(f911,plain,(
% 4.70/0.95    spl4_112 <=> ! [X1,X0] : (~v1_tsep_1(k1_tsep_1(sK0,X0,X0),X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~m1_pre_topc(k1_tsep_1(sK0,X0,X0),X1) | v1_tsep_1(X0,X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).
% 4.70/0.95  fof(f2851,plain,(
% 4.70/0.95    spl4_315 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_315])])).
% 4.70/0.95  fof(f3279,plain,(
% 4.70/0.95    spl4_347 <=> v1_tsep_1(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_347])])).
% 4.70/0.95  fof(f3291,plain,(
% 4.70/0.95    ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | (spl4_3 | ~spl4_12 | spl4_17 | ~spl4_112 | ~spl4_315 | ~spl4_347)),
% 4.70/0.95    inference(subsumption_resolution,[],[f3290,f108])).
% 4.70/0.95  fof(f3290,plain,(
% 4.70/0.95    ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK1) | (~spl4_12 | spl4_17 | ~spl4_112 | ~spl4_315 | ~spl4_347)),
% 4.70/0.95    inference(subsumption_resolution,[],[f3289,f144])).
% 4.70/0.95  fof(f3289,plain,(
% 4.70/0.95    ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | (spl4_17 | ~spl4_112 | ~spl4_315 | ~spl4_347)),
% 4.70/0.95    inference(subsumption_resolution,[],[f3288,f161])).
% 4.70/0.95  fof(f161,plain,(
% 4.70/0.95    ~v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) | spl4_17),
% 4.70/0.95    inference(avatar_component_clause,[],[f160])).
% 4.70/0.95  fof(f3288,plain,(
% 4.70/0.95    ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | (~spl4_112 | ~spl4_315 | ~spl4_347)),
% 4.70/0.95    inference(subsumption_resolution,[],[f3283,f2852])).
% 4.70/0.95  fof(f2852,plain,(
% 4.70/0.95    m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) | ~spl4_315),
% 4.70/0.95    inference(avatar_component_clause,[],[f2851])).
% 4.70/0.95  fof(f3283,plain,(
% 4.70/0.95    ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) | v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | (~spl4_112 | ~spl4_347)),
% 4.70/0.95    inference(resolution,[],[f3280,f912])).
% 4.70/0.95  fof(f912,plain,(
% 4.70/0.95    ( ! [X0,X1] : (~v1_tsep_1(k1_tsep_1(sK0,X0,X0),X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~m1_pre_topc(k1_tsep_1(sK0,X0,X0),X1) | v1_tsep_1(X0,X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | ~spl4_112),
% 4.70/0.95    inference(avatar_component_clause,[],[f911])).
% 4.70/0.95  fof(f3280,plain,(
% 4.70/0.95    v1_tsep_1(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) | ~spl4_347),
% 4.70/0.95    inference(avatar_component_clause,[],[f3279])).
% 4.70/0.95  fof(f3281,plain,(
% 4.70/0.95    spl4_314 | ~spl4_98 | spl4_97 | spl4_347 | spl4_1 | spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_12 | ~spl4_27 | ~spl4_35 | ~spl4_111 | ~spl4_202 | ~spl4_206),
% 4.70/0.95    inference(avatar_split_clause,[],[f1713,f1693,f1658,f907,f257,f204,f143,f131,f127,f123,f119,f115,f111,f107,f99,f3279,f785,f788,f2848])).
% 4.70/0.95  fof(f2848,plain,(
% 4.70/0.95    spl4_314 <=> r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_314])])).
% 4.70/0.95  fof(f785,plain,(
% 4.70/0.95    spl4_97 <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_97])])).
% 4.70/0.95  fof(f99,plain,(
% 4.70/0.95    spl4_1 <=> v2_struct_0(sK3)),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 4.70/0.95  fof(f123,plain,(
% 4.70/0.95    spl4_7 <=> v1_tsep_1(sK3,sK0)),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 4.70/0.95  fof(f127,plain,(
% 4.70/0.95    spl4_8 <=> m1_pre_topc(sK3,sK0)),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 4.70/0.95  fof(f131,plain,(
% 4.70/0.95    spl4_9 <=> m1_pre_topc(sK1,sK3)),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 4.70/0.95  fof(f204,plain,(
% 4.70/0.95    spl4_27 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 4.70/0.95  fof(f257,plain,(
% 4.70/0.95    spl4_35 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X2,X1) | v1_tsep_1(k2_tsep_1(X0,X2,X1),X1))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 4.70/0.95  fof(f907,plain,(
% 4.70/0.95    spl4_111 <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_111])])).
% 4.70/0.95  fof(f1658,plain,(
% 4.70/0.95    spl4_202 <=> ! [X7] : (k1_tsep_1(sK3,X7,X7) = g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) | ~m1_pre_topc(X7,sK3) | v2_struct_0(X7))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_202])])).
% 4.70/0.95  fof(f1693,plain,(
% 4.70/0.95    spl4_206 <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK3,sK1,sK1)),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_206])])).
% 4.70/0.95  fof(f1713,plain,(
% 4.70/0.95    v1_tsep_1(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | (spl4_1 | spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_12 | ~spl4_27 | ~spl4_35 | ~spl4_111 | ~spl4_202 | ~spl4_206)),
% 4.70/0.95    inference(backward_demodulation,[],[f1675,f1709])).
% 4.70/0.95  fof(f1709,plain,(
% 4.70/0.95    k1_tsep_1(sK0,sK1,sK1) = k1_tsep_1(sK3,sK1,sK1) | (spl4_3 | ~spl4_12 | ~spl4_27 | ~spl4_206)),
% 4.70/0.95    inference(subsumption_resolution,[],[f1708,f108])).
% 4.70/0.95  fof(f1708,plain,(
% 4.70/0.95    k1_tsep_1(sK0,sK1,sK1) = k1_tsep_1(sK3,sK1,sK1) | v2_struct_0(sK1) | (~spl4_12 | ~spl4_27 | ~spl4_206)),
% 4.70/0.95    inference(subsumption_resolution,[],[f1700,f144])).
% 4.70/0.95  fof(f1700,plain,(
% 4.70/0.95    k1_tsep_1(sK0,sK1,sK1) = k1_tsep_1(sK3,sK1,sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | (~spl4_27 | ~spl4_206)),
% 4.70/0.95    inference(superposition,[],[f1694,f205])).
% 4.70/0.95  fof(f205,plain,(
% 4.70/0.95    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | ~spl4_27),
% 4.70/0.95    inference(avatar_component_clause,[],[f204])).
% 4.70/0.95  fof(f1694,plain,(
% 4.70/0.95    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK3,sK1,sK1) | ~spl4_206),
% 4.70/0.95    inference(avatar_component_clause,[],[f1693])).
% 4.70/0.95  fof(f1675,plain,(
% 4.70/0.95    v1_tsep_1(k1_tsep_1(sK3,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | (spl4_1 | spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_35 | ~spl4_111 | ~spl4_202)),
% 4.70/0.95    inference(backward_demodulation,[],[f921,f1674])).
% 4.70/0.95  fof(f1674,plain,(
% 4.70/0.95    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK3,sK1,sK1) | (spl4_3 | ~spl4_9 | ~spl4_202)),
% 4.70/0.95    inference(subsumption_resolution,[],[f1671,f132])).
% 4.70/0.95  fof(f132,plain,(
% 4.70/0.95    m1_pre_topc(sK1,sK3) | ~spl4_9),
% 4.70/0.95    inference(avatar_component_clause,[],[f131])).
% 4.70/0.95  fof(f1671,plain,(
% 4.70/0.95    ~m1_pre_topc(sK1,sK3) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK3,sK1,sK1) | (spl4_3 | ~spl4_202)),
% 4.70/0.95    inference(resolution,[],[f1659,f108])).
% 4.70/0.95  fof(f1659,plain,(
% 4.70/0.95    ( ! [X7] : (v2_struct_0(X7) | ~m1_pre_topc(X7,sK3) | k1_tsep_1(sK3,X7,X7) = g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))) ) | ~spl4_202),
% 4.70/0.95    inference(avatar_component_clause,[],[f1658])).
% 4.70/0.95  fof(f921,plain,(
% 4.70/0.95    v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | (spl4_1 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_35 | ~spl4_111)),
% 4.70/0.95    inference(subsumption_resolution,[],[f920,f112])).
% 4.70/0.95  fof(f920,plain,(
% 4.70/0.95    v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0) | (spl4_1 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_35 | ~spl4_111)),
% 4.70/0.95    inference(subsumption_resolution,[],[f919,f128])).
% 4.70/0.95  fof(f128,plain,(
% 4.70/0.95    m1_pre_topc(sK3,sK0) | ~spl4_8),
% 4.70/0.95    inference(avatar_component_clause,[],[f127])).
% 4.70/0.95  fof(f919,plain,(
% 4.70/0.95    v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | ~m1_pre_topc(sK3,sK0) | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0) | (spl4_1 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_35 | ~spl4_111)),
% 4.70/0.95    inference(subsumption_resolution,[],[f918,f124])).
% 4.70/0.95  fof(f124,plain,(
% 4.70/0.95    v1_tsep_1(sK3,sK0) | ~spl4_7),
% 4.70/0.95    inference(avatar_component_clause,[],[f123])).
% 4.70/0.95  fof(f918,plain,(
% 4.70/0.95    v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | ~v1_tsep_1(sK3,sK0) | ~m1_pre_topc(sK3,sK0) | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0) | (spl4_1 | ~spl4_5 | ~spl4_6 | ~spl4_35 | ~spl4_111)),
% 4.70/0.95    inference(subsumption_resolution,[],[f917,f100])).
% 4.70/0.95  fof(f100,plain,(
% 4.70/0.95    ~v2_struct_0(sK3) | spl4_1),
% 4.70/0.95    inference(avatar_component_clause,[],[f99])).
% 4.70/0.95  fof(f917,plain,(
% 4.70/0.95    v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK3) | ~v1_tsep_1(sK3,sK0) | ~m1_pre_topc(sK3,sK0) | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0) | (~spl4_5 | ~spl4_6 | ~spl4_35 | ~spl4_111)),
% 4.70/0.95    inference(subsumption_resolution,[],[f916,f120])).
% 4.70/0.95  fof(f916,plain,(
% 4.70/0.95    v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK3) | ~v1_tsep_1(sK3,sK0) | ~m1_pre_topc(sK3,sK0) | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0) | (~spl4_5 | ~spl4_35 | ~spl4_111)),
% 4.70/0.95    inference(subsumption_resolution,[],[f915,f116])).
% 4.70/0.95  fof(f915,plain,(
% 4.70/0.95    v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK3) | ~v1_tsep_1(sK3,sK0) | ~m1_pre_topc(sK3,sK0) | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0) | (~spl4_35 | ~spl4_111)),
% 4.70/0.95    inference(superposition,[],[f258,f908])).
% 4.70/0.95  fof(f908,plain,(
% 4.70/0.95    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2)) | ~spl4_111),
% 4.70/0.95    inference(avatar_component_clause,[],[f907])).
% 4.70/0.95  fof(f258,plain,(
% 4.70/0.95    ( ! [X2,X0,X1] : (v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X2,X1) | v2_struct_0(X0)) ) | ~spl4_35),
% 4.70/0.95    inference(avatar_component_clause,[],[f257])).
% 4.70/0.95  fof(f3223,plain,(
% 4.70/0.95    ~spl4_6 | ~spl4_12 | ~spl4_13 | spl4_341),
% 4.70/0.95    inference(avatar_contradiction_clause,[],[f3221])).
% 4.70/0.95  fof(f3221,plain,(
% 4.70/0.95    $false | (~spl4_6 | ~spl4_12 | ~spl4_13 | spl4_341)),
% 4.70/0.95    inference(unit_resulting_resolution,[],[f120,f144,f3216,f148])).
% 4.70/0.95  fof(f3216,plain,(
% 4.70/0.95    ~l1_pre_topc(sK1) | spl4_341),
% 4.70/0.95    inference(avatar_component_clause,[],[f3215])).
% 4.70/0.95  fof(f2928,plain,(
% 4.70/0.95    spl4_294 | spl4_1 | spl4_2 | spl4_3 | ~spl4_8 | ~spl4_11 | ~spl4_12 | ~spl4_60 | ~spl4_314),
% 4.70/0.95    inference(avatar_split_clause,[],[f2884,f2848,f477,f143,f139,f127,f107,f103,f99,f2569])).
% 4.70/0.95  fof(f2569,plain,(
% 4.70/0.95    spl4_294 <=> r1_tsep_1(sK3,sK1)),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_294])])).
% 4.70/0.95  fof(f477,plain,(
% 4.70/0.95    spl4_60 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK0) | r1_tsep_1(X2,X0) | ~r1_tsep_1(X2,k1_tsep_1(sK0,X0,X1)))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 4.70/0.95  fof(f2884,plain,(
% 4.70/0.95    r1_tsep_1(sK3,sK1) | (spl4_1 | spl4_2 | spl4_3 | ~spl4_8 | ~spl4_11 | ~spl4_12 | ~spl4_60 | ~spl4_314)),
% 4.70/0.95    inference(subsumption_resolution,[],[f2883,f108])).
% 4.70/0.95  fof(f2883,plain,(
% 4.70/0.95    r1_tsep_1(sK3,sK1) | v2_struct_0(sK1) | (spl4_1 | spl4_2 | ~spl4_8 | ~spl4_11 | ~spl4_12 | ~spl4_60 | ~spl4_314)),
% 4.70/0.95    inference(subsumption_resolution,[],[f2882,f128])).
% 4.70/0.95  fof(f2882,plain,(
% 4.70/0.95    ~m1_pre_topc(sK3,sK0) | r1_tsep_1(sK3,sK1) | v2_struct_0(sK1) | (spl4_1 | spl4_2 | ~spl4_11 | ~spl4_12 | ~spl4_60 | ~spl4_314)),
% 4.70/0.95    inference(subsumption_resolution,[],[f2881,f100])).
% 4.70/0.95  fof(f2881,plain,(
% 4.70/0.95    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | r1_tsep_1(sK3,sK1) | v2_struct_0(sK1) | (spl4_2 | ~spl4_11 | ~spl4_12 | ~spl4_60 | ~spl4_314)),
% 4.70/0.95    inference(subsumption_resolution,[],[f2880,f140])).
% 4.70/0.95  fof(f2880,plain,(
% 4.70/0.95    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | r1_tsep_1(sK3,sK1) | v2_struct_0(sK1) | (spl4_2 | ~spl4_12 | ~spl4_60 | ~spl4_314)),
% 4.70/0.95    inference(subsumption_resolution,[],[f2879,f104])).
% 4.70/0.95  fof(f2879,plain,(
% 4.70/0.95    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | r1_tsep_1(sK3,sK1) | v2_struct_0(sK1) | (~spl4_12 | ~spl4_60 | ~spl4_314)),
% 4.70/0.95    inference(subsumption_resolution,[],[f2870,f144])).
% 4.70/0.95  fof(f2870,plain,(
% 4.70/0.95    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | r1_tsep_1(sK3,sK1) | v2_struct_0(sK1) | (~spl4_60 | ~spl4_314)),
% 4.70/0.95    inference(resolution,[],[f2849,f478])).
% 4.70/0.95  fof(f478,plain,(
% 4.70/0.95    ( ! [X2,X0,X1] : (~r1_tsep_1(X2,k1_tsep_1(sK0,X0,X1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK0) | r1_tsep_1(X2,X0) | v2_struct_0(X0)) ) | ~spl4_60),
% 4.70/0.95    inference(avatar_component_clause,[],[f477])).
% 4.70/0.95  fof(f2849,plain,(
% 4.70/0.95    r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | ~spl4_314),
% 4.70/0.95    inference(avatar_component_clause,[],[f2848])).
% 4.70/0.95  fof(f2867,plain,(
% 4.70/0.95    spl4_2 | spl4_3 | spl4_4 | ~spl4_6 | ~spl4_11 | ~spl4_12 | ~spl4_19 | ~spl4_97),
% 4.70/0.95    inference(avatar_contradiction_clause,[],[f2866])).
% 4.70/0.95  fof(f2866,plain,(
% 4.70/0.95    $false | (spl4_2 | spl4_3 | spl4_4 | ~spl4_6 | ~spl4_11 | ~spl4_12 | ~spl4_19 | ~spl4_97)),
% 4.70/0.95    inference(subsumption_resolution,[],[f2865,f112])).
% 4.70/0.95  fof(f2865,plain,(
% 4.70/0.95    v2_struct_0(sK0) | (spl4_2 | spl4_3 | ~spl4_6 | ~spl4_11 | ~spl4_12 | ~spl4_19 | ~spl4_97)),
% 4.70/0.95    inference(subsumption_resolution,[],[f2864,f140])).
% 4.70/0.95  fof(f2864,plain,(
% 4.70/0.95    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl4_2 | spl4_3 | ~spl4_6 | ~spl4_12 | ~spl4_19 | ~spl4_97)),
% 4.70/0.95    inference(subsumption_resolution,[],[f2863,f104])).
% 4.70/0.95  fof(f2863,plain,(
% 4.70/0.95    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl4_3 | ~spl4_6 | ~spl4_12 | ~spl4_19 | ~spl4_97)),
% 4.70/0.95    inference(subsumption_resolution,[],[f2862,f144])).
% 4.70/0.95  fof(f2862,plain,(
% 4.70/0.95    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl4_3 | ~spl4_6 | ~spl4_19 | ~spl4_97)),
% 4.70/0.95    inference(subsumption_resolution,[],[f2861,f108])).
% 4.70/0.95  fof(f2861,plain,(
% 4.70/0.95    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl4_6 | ~spl4_19 | ~spl4_97)),
% 4.70/0.95    inference(subsumption_resolution,[],[f2859,f120])).
% 4.70/0.95  fof(f2859,plain,(
% 4.70/0.95    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl4_19 | ~spl4_97)),
% 4.70/0.95    inference(resolution,[],[f786,f169])).
% 4.70/0.95  fof(f169,plain,(
% 4.70/0.95    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) ) | ~spl4_19),
% 4.70/0.95    inference(avatar_component_clause,[],[f168])).
% 4.70/0.95  fof(f168,plain,(
% 4.70/0.95    spl4_19 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~v2_struct_0(k1_tsep_1(X0,X1,X2)))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 4.70/0.95  fof(f786,plain,(
% 4.70/0.95    v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~spl4_97),
% 4.70/0.95    inference(avatar_component_clause,[],[f785])).
% 4.70/0.95  fof(f2853,plain,(
% 4.70/0.95    ~spl4_98 | spl4_314 | spl4_97 | spl4_315 | spl4_3 | ~spl4_9 | ~spl4_12 | ~spl4_27 | ~spl4_61 | ~spl4_111 | ~spl4_202 | ~spl4_206),
% 4.70/0.95    inference(avatar_split_clause,[],[f1712,f1693,f1658,f907,f484,f204,f143,f131,f107,f2851,f785,f2848,f788])).
% 4.70/0.95  fof(f484,plain,(
% 4.70/0.95    spl4_61 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(sK3,X0) | m1_pre_topc(k2_tsep_1(sK0,sK3,X0),X0))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 4.70/0.95  fof(f1712,plain,(
% 4.70/0.95    m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | (spl4_3 | ~spl4_9 | ~spl4_12 | ~spl4_27 | ~spl4_61 | ~spl4_111 | ~spl4_202 | ~spl4_206)),
% 4.70/0.95    inference(backward_demodulation,[],[f1676,f1709])).
% 4.70/0.95  fof(f1676,plain,(
% 4.70/0.95    m1_pre_topc(k1_tsep_1(sK3,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | (spl4_3 | ~spl4_9 | ~spl4_61 | ~spl4_111 | ~spl4_202)),
% 4.70/0.95    inference(backward_demodulation,[],[f914,f1674])).
% 4.70/0.95  fof(f914,plain,(
% 4.70/0.95    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | (~spl4_61 | ~spl4_111)),
% 4.70/0.95    inference(superposition,[],[f485,f908])).
% 4.70/0.95  fof(f485,plain,(
% 4.70/0.95    ( ! [X0] : (m1_pre_topc(k2_tsep_1(sK0,sK3,X0),X0) | v2_struct_0(X0) | r1_tsep_1(sK3,X0) | ~m1_pre_topc(X0,sK0)) ) | ~spl4_61),
% 4.70/0.95    inference(avatar_component_clause,[],[f484])).
% 4.70/0.95  fof(f2588,plain,(
% 4.70/0.95    spl4_1 | spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_9 | ~spl4_12 | ~spl4_26 | ~spl4_294),
% 4.70/0.95    inference(avatar_contradiction_clause,[],[f2578])).
% 4.70/0.95  fof(f2578,plain,(
% 4.70/0.95    $false | (spl4_1 | spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_9 | ~spl4_12 | ~spl4_26 | ~spl4_294)),
% 4.70/0.95    inference(unit_resulting_resolution,[],[f112,f116,f120,f100,f128,f144,f108,f132,f2570,f197])).
% 4.70/0.95  fof(f197,plain,(
% 4.70/0.95    ( ! [X2,X0,X1] : (~r1_tsep_1(X2,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | v2_struct_0(X0)) ) | ~spl4_26),
% 4.70/0.95    inference(avatar_component_clause,[],[f196])).
% 4.70/0.95  fof(f196,plain,(
% 4.70/0.95    spl4_26 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | ~r1_tsep_1(X2,X1))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 4.70/0.95  fof(f2570,plain,(
% 4.70/0.95    r1_tsep_1(sK3,sK1) | ~spl4_294),
% 4.70/0.95    inference(avatar_component_clause,[],[f2569])).
% 4.70/0.95  fof(f1695,plain,(
% 4.70/0.95    spl4_206 | spl4_3 | ~spl4_9 | ~spl4_202),
% 4.70/0.95    inference(avatar_split_clause,[],[f1674,f1658,f131,f107,f1693])).
% 4.70/0.95  fof(f1660,plain,(
% 4.70/0.95    spl4_202 | spl4_1 | ~spl4_8 | ~spl4_195),
% 4.70/0.95    inference(avatar_split_clause,[],[f1612,f1593,f127,f99,f1658])).
% 4.70/0.95  fof(f1593,plain,(
% 4.70/0.95    spl4_195 <=> ! [X1,X0] : (~m1_pre_topc(X0,X1) | k1_tsep_1(X1,X0,X0) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(X0))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_195])])).
% 4.70/0.95  fof(f1612,plain,(
% 4.70/0.95    ( ! [X7] : (k1_tsep_1(sK3,X7,X7) = g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) | ~m1_pre_topc(X7,sK3) | v2_struct_0(X7)) ) | (spl4_1 | ~spl4_8 | ~spl4_195)),
% 4.70/0.95    inference(subsumption_resolution,[],[f1608,f128])).
% 4.70/0.95  fof(f1608,plain,(
% 4.70/0.95    ( ! [X7] : (k1_tsep_1(sK3,X7,X7) = g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(X7,sK3) | v2_struct_0(X7)) ) | (spl4_1 | ~spl4_195)),
% 4.70/0.95    inference(resolution,[],[f1594,f100])).
% 4.70/0.95  fof(f1594,plain,(
% 4.70/0.95    ( ! [X0,X1] : (v2_struct_0(X1) | k1_tsep_1(X1,X0,X0) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0)) ) | ~spl4_195),
% 4.70/0.95    inference(avatar_component_clause,[],[f1593])).
% 4.70/0.95  fof(f1595,plain,(
% 4.70/0.95    spl4_195 | ~spl4_5 | ~spl4_6 | ~spl4_173),
% 4.70/0.95    inference(avatar_split_clause,[],[f1332,f1319,f119,f115,f1593])).
% 4.70/0.95  fof(f1319,plain,(
% 4.70/0.95    spl4_173 <=> ! [X1,X3,X2] : (v2_struct_0(X1) | ~m1_pre_topc(X1,X2) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X2,X1,X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~m1_pre_topc(X2,X3) | ~v2_pre_topc(X3))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_173])])).
% 4.70/0.95  fof(f1332,plain,(
% 4.70/0.95    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | k1_tsep_1(X1,X0,X0) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(X0)) ) | (~spl4_5 | ~spl4_6 | ~spl4_173)),
% 4.70/0.95    inference(subsumption_resolution,[],[f1331,f116])).
% 4.70/0.95  fof(f1331,plain,(
% 4.70/0.95    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | k1_tsep_1(X1,X0,X0) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(X0) | ~v2_pre_topc(sK0)) ) | (~spl4_6 | ~spl4_173)),
% 4.70/0.95    inference(duplicate_literal_removal,[],[f1329])).
% 4.70/0.95  fof(f1329,plain,(
% 4.70/0.95    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | k1_tsep_1(X1,X0,X0) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | ~v2_pre_topc(sK0)) ) | (~spl4_6 | ~spl4_173)),
% 4.70/0.95    inference(resolution,[],[f1320,f120])).
% 4.70/0.95  fof(f1320,plain,(
% 4.70/0.95    ( ! [X2,X3,X1] : (~l1_pre_topc(X3) | ~m1_pre_topc(X1,X2) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X2,X1,X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | v2_struct_0(X1) | ~m1_pre_topc(X2,X3) | ~v2_pre_topc(X3)) ) | ~spl4_173),
% 4.70/0.95    inference(avatar_component_clause,[],[f1319])).
% 4.70/0.95  fof(f1321,plain,(
% 4.70/0.95    spl4_173 | ~spl4_18 | ~spl4_99),
% 4.70/0.95    inference(avatar_split_clause,[],[f796,f792,f164,f1319])).
% 4.70/0.95  fof(f792,plain,(
% 4.70/0.95    spl4_99 <=> ! [X1,X0] : (v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X0,sK0) | ~v2_pre_topc(X0))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).
% 4.70/0.95  fof(f796,plain,(
% 4.70/0.95    ( ! [X2,X3,X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,X2) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X2,X1,X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~m1_pre_topc(X2,X3) | ~v2_pre_topc(X3)) ) | (~spl4_18 | ~spl4_99)),
% 4.70/0.95    inference(resolution,[],[f793,f165])).
% 4.70/0.95  fof(f793,plain,(
% 4.70/0.95    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | ~spl4_99),
% 4.70/0.95    inference(avatar_component_clause,[],[f792])).
% 4.70/0.95  fof(f913,plain,(
% 4.70/0.95    spl4_112 | ~spl4_27 | ~spl4_31),
% 4.70/0.95    inference(avatar_split_clause,[],[f250,f239,f204,f911])).
% 4.70/0.95  fof(f239,plain,(
% 4.70/0.95    spl4_31 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | v1_tsep_1(X1,X0))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 4.70/0.95  fof(f250,plain,(
% 4.70/0.95    ( ! [X0,X1] : (~v1_tsep_1(k1_tsep_1(sK0,X0,X0),X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~m1_pre_topc(k1_tsep_1(sK0,X0,X0),X1) | v1_tsep_1(X0,X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | (~spl4_27 | ~spl4_31)),
% 4.70/0.95    inference(superposition,[],[f240,f205])).
% 4.70/0.95  fof(f240,plain,(
% 4.70/0.95    ( ! [X0,X1] : (~v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | v1_tsep_1(X1,X0)) ) | ~spl4_31),
% 4.70/0.95    inference(avatar_component_clause,[],[f239])).
% 4.70/0.95  fof(f909,plain,(
% 4.70/0.95    spl4_111 | spl4_3 | ~spl4_9 | ~spl4_12 | ~spl4_109),
% 4.70/0.95    inference(avatar_split_clause,[],[f891,f882,f143,f131,f107,f907])).
% 4.70/0.95  fof(f882,plain,(
% 4.70/0.95    spl4_109 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,sK3) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,X0,sK2)))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_109])])).
% 4.70/0.95  fof(f891,plain,(
% 4.70/0.95    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2)) | (spl4_3 | ~spl4_9 | ~spl4_12 | ~spl4_109)),
% 4.70/0.95    inference(subsumption_resolution,[],[f890,f132])).
% 4.70/0.95  fof(f890,plain,(
% 4.70/0.95    ~m1_pre_topc(sK1,sK3) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2)) | (spl4_3 | ~spl4_12 | ~spl4_109)),
% 4.70/0.95    inference(subsumption_resolution,[],[f887,f144])).
% 4.70/0.95  fof(f887,plain,(
% 4.70/0.95    ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK1,sK3) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2)) | (spl4_3 | ~spl4_109)),
% 4.70/0.95    inference(resolution,[],[f883,f108])).
% 4.70/0.95  fof(f883,plain,(
% 4.70/0.95    ( ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,sK3) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,X0,sK2))) ) | ~spl4_109),
% 4.70/0.95    inference(avatar_component_clause,[],[f882])).
% 4.70/0.95  fof(f884,plain,(
% 4.70/0.95    spl4_109 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_73),
% 4.70/0.95    inference(avatar_split_clause,[],[f624,f612,f139,f127,f119,f115,f111,f882])).
% 4.70/0.95  fof(f612,plain,(
% 4.70/0.95    spl4_73 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,sK3,k1_tsep_1(X0,X1,sK2)))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 4.70/0.95  fof(f624,plain,(
% 4.70/0.95    ( ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,sK3) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,X0,sK2))) ) | (spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_73)),
% 4.70/0.95    inference(subsumption_resolution,[],[f623,f112])).
% 4.70/0.95  fof(f623,plain,(
% 4.70/0.95    ( ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,X0,sK2))) ) | (~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_73)),
% 4.70/0.95    inference(subsumption_resolution,[],[f622,f140])).
% 4.70/0.95  fof(f622,plain,(
% 4.70/0.95    ( ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,X0,sK2))) ) | (~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_73)),
% 4.70/0.95    inference(subsumption_resolution,[],[f621,f128])).
% 4.70/0.95  fof(f621,plain,(
% 4.70/0.95    ( ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,X0,sK2))) ) | (~spl4_5 | ~spl4_6 | ~spl4_73)),
% 4.70/0.95    inference(subsumption_resolution,[],[f619,f116])).
% 4.70/0.95  fof(f619,plain,(
% 4.70/0.95    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,X0,sK2))) ) | (~spl4_6 | ~spl4_73)),
% 4.70/0.95    inference(resolution,[],[f613,f120])).
% 4.70/0.95  fof(f613,plain,(
% 4.70/0.95    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,sK3,k1_tsep_1(X0,X1,sK2))) ) | ~spl4_73),
% 4.70/0.95    inference(avatar_component_clause,[],[f612])).
% 4.70/0.95  fof(f808,plain,(
% 4.70/0.95    spl4_2 | spl4_3 | spl4_4 | ~spl4_6 | ~spl4_11 | ~spl4_12 | ~spl4_21 | spl4_98),
% 4.70/0.95    inference(avatar_contradiction_clause,[],[f807])).
% 4.70/0.95  fof(f807,plain,(
% 4.70/0.95    $false | (spl4_2 | spl4_3 | spl4_4 | ~spl4_6 | ~spl4_11 | ~spl4_12 | ~spl4_21 | spl4_98)),
% 4.70/0.95    inference(subsumption_resolution,[],[f806,f112])).
% 4.70/0.95  fof(f806,plain,(
% 4.70/0.95    v2_struct_0(sK0) | (spl4_2 | spl4_3 | ~spl4_6 | ~spl4_11 | ~spl4_12 | ~spl4_21 | spl4_98)),
% 4.70/0.95    inference(subsumption_resolution,[],[f805,f140])).
% 4.70/0.95  fof(f805,plain,(
% 4.70/0.95    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl4_2 | spl4_3 | ~spl4_6 | ~spl4_12 | ~spl4_21 | spl4_98)),
% 4.70/0.95    inference(subsumption_resolution,[],[f804,f104])).
% 4.70/0.95  fof(f804,plain,(
% 4.70/0.95    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl4_3 | ~spl4_6 | ~spl4_12 | ~spl4_21 | spl4_98)),
% 4.70/0.95    inference(subsumption_resolution,[],[f803,f144])).
% 4.70/0.95  fof(f803,plain,(
% 4.70/0.95    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl4_3 | ~spl4_6 | ~spl4_21 | spl4_98)),
% 4.70/0.95    inference(subsumption_resolution,[],[f802,f108])).
% 4.70/0.95  fof(f802,plain,(
% 4.70/0.95    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl4_6 | ~spl4_21 | spl4_98)),
% 4.70/0.95    inference(subsumption_resolution,[],[f800,f120])).
% 4.70/0.95  fof(f800,plain,(
% 4.70/0.95    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl4_21 | spl4_98)),
% 4.70/0.95    inference(resolution,[],[f789,f177])).
% 4.70/0.95  fof(f177,plain,(
% 4.70/0.95    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) ) | ~spl4_21),
% 4.70/0.95    inference(avatar_component_clause,[],[f176])).
% 4.70/0.95  fof(f176,plain,(
% 4.70/0.95    spl4_21 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 4.70/0.95  fof(f789,plain,(
% 4.70/0.95    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | spl4_98),
% 4.70/0.95    inference(avatar_component_clause,[],[f788])).
% 4.70/0.95  fof(f794,plain,(
% 4.70/0.95    spl4_99 | ~spl4_6 | ~spl4_77),
% 4.70/0.95    inference(avatar_split_clause,[],[f650,f640,f119,f792])).
% 4.70/0.95  fof(f640,plain,(
% 4.70/0.95    spl4_77 <=> ! [X1,X3,X2] : (~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X1,X2,X2) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X3))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).
% 4.70/0.95  fof(f650,plain,(
% 4.70/0.95    ( ! [X0,X1] : (v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X0,sK0) | ~v2_pre_topc(X0)) ) | (~spl4_6 | ~spl4_77)),
% 4.70/0.95    inference(resolution,[],[f641,f120])).
% 4.70/0.95  fof(f641,plain,(
% 4.70/0.95    ( ! [X2,X3,X1] : (~l1_pre_topc(X3) | v2_struct_0(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X1,X2,X2) | ~m1_pre_topc(X1,X3) | ~v2_pre_topc(X1)) ) | ~spl4_77),
% 4.70/0.95    inference(avatar_component_clause,[],[f640])).
% 4.70/0.95  fof(f642,plain,(
% 4.70/0.95    spl4_77 | ~spl4_13 | ~spl4_22),
% 4.70/0.95    inference(avatar_split_clause,[],[f200,f180,f147,f640])).
% 4.70/0.95  fof(f180,plain,(
% 4.70/0.95    spl4_22 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 4.70/0.95  fof(f200,plain,(
% 4.70/0.95    ( ! [X2,X3,X1] : (~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X1,X2,X2) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X3)) ) | (~spl4_13 | ~spl4_22)),
% 4.70/0.95    inference(resolution,[],[f181,f148])).
% 4.70/0.95  fof(f181,plain,(
% 4.70/0.95    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)) ) | ~spl4_22),
% 4.70/0.95    inference(avatar_component_clause,[],[f180])).
% 4.70/0.95  fof(f614,plain,(
% 4.70/0.95    spl4_73 | spl4_1 | spl4_2 | ~spl4_10 | ~spl4_56),
% 4.70/0.95    inference(avatar_split_clause,[],[f463,f438,f135,f103,f99,f612])).
% 4.70/0.95  fof(f135,plain,(
% 4.70/0.95    spl4_10 <=> r1_tsep_1(sK3,sK2)),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 4.70/0.95  fof(f438,plain,(
% 4.70/0.95    spl4_56 <=> ! [X1,X3,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X1,X2) | ~r1_tsep_1(X2,X3) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)))),
% 4.70/0.95    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 4.70/0.95  fof(f463,plain,(
% 4.70/0.95    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,sK3,k1_tsep_1(X0,X1,sK2))) ) | (spl4_1 | spl4_2 | ~spl4_10 | ~spl4_56)),
% 4.70/0.95    inference(subsumption_resolution,[],[f462,f104])).
% 4.70/0.95  fof(f462,plain,(
% 4.70/0.95    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,sK3,k1_tsep_1(X0,X1,sK2))) ) | (spl4_1 | ~spl4_10 | ~spl4_56)),
% 4.70/0.95    inference(subsumption_resolution,[],[f461,f100])).
% 4.70/0.97  fof(f461,plain,(
% 4.70/0.97    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,sK3,k1_tsep_1(X0,X1,sK2))) ) | (~spl4_10 | ~spl4_56)),
% 4.70/0.97    inference(resolution,[],[f439,f136])).
% 4.70/0.97  fof(f136,plain,(
% 4.70/0.97    r1_tsep_1(sK3,sK2) | ~spl4_10),
% 4.70/0.97    inference(avatar_component_clause,[],[f135])).
% 4.70/0.97  fof(f439,plain,(
% 4.70/0.97    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X2,X3) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X1,X2) | v2_struct_0(X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))) ) | ~spl4_56),
% 4.70/0.97    inference(avatar_component_clause,[],[f438])).
% 4.70/0.97  fof(f486,plain,(
% 4.70/0.97    spl4_61 | spl4_1 | ~spl4_7 | ~spl4_8 | ~spl4_59),
% 4.70/0.97    inference(avatar_split_clause,[],[f474,f465,f127,f123,f99,f484])).
% 4.70/0.97  fof(f465,plain,(
% 4.70/0.97    spl4_59 <=> ! [X1,X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~v1_tsep_1(X1,sK0) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(X1,X0) | m1_pre_topc(k2_tsep_1(sK0,X1,X0),X0))),
% 4.70/0.97    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 4.70/0.97  fof(f474,plain,(
% 4.70/0.97    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(sK3,X0) | m1_pre_topc(k2_tsep_1(sK0,sK3,X0),X0)) ) | (spl4_1 | ~spl4_7 | ~spl4_8 | ~spl4_59)),
% 4.70/0.97    inference(subsumption_resolution,[],[f473,f128])).
% 4.70/0.97  fof(f473,plain,(
% 4.70/0.97    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK3,sK0) | r1_tsep_1(sK3,X0) | m1_pre_topc(k2_tsep_1(sK0,sK3,X0),X0)) ) | (spl4_1 | ~spl4_7 | ~spl4_59)),
% 4.70/0.97    inference(subsumption_resolution,[],[f471,f100])).
% 4.70/0.97  fof(f471,plain,(
% 4.70/0.97    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(sK3) | v2_struct_0(X0) | ~m1_pre_topc(sK3,sK0) | r1_tsep_1(sK3,X0) | m1_pre_topc(k2_tsep_1(sK0,sK3,X0),X0)) ) | (~spl4_7 | ~spl4_59)),
% 4.70/0.97    inference(resolution,[],[f466,f124])).
% 4.70/0.97  fof(f466,plain,(
% 4.70/0.97    ( ! [X0,X1] : (~v1_tsep_1(X1,sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(X1,X0) | m1_pre_topc(k2_tsep_1(sK0,X1,X0),X0)) ) | ~spl4_59),
% 4.70/0.97    inference(avatar_component_clause,[],[f465])).
% 4.70/0.97  fof(f479,plain,(
% 4.70/0.97    spl4_60 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_41),
% 4.70/0.97    inference(avatar_split_clause,[],[f359,f317,f119,f115,f111,f477])).
% 4.70/0.97  fof(f317,plain,(
% 4.70/0.97    spl4_41 <=> ! [X1,X3,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | r1_tsep_1(X3,X1) | ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)))),
% 4.70/0.97    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 4.70/0.97  fof(f359,plain,(
% 4.70/0.97    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK0) | r1_tsep_1(X2,X0) | ~r1_tsep_1(X2,k1_tsep_1(sK0,X0,X1))) ) | (spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_41)),
% 4.70/0.97    inference(subsumption_resolution,[],[f358,f112])).
% 4.70/0.97  fof(f358,plain,(
% 4.70/0.97    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK0) | r1_tsep_1(X2,X0) | ~r1_tsep_1(X2,k1_tsep_1(sK0,X0,X1))) ) | (~spl4_5 | ~spl4_6 | ~spl4_41)),
% 4.70/0.97    inference(subsumption_resolution,[],[f356,f116])).
% 4.70/0.97  fof(f356,plain,(
% 4.70/0.97    ( ! [X2,X0,X1] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK0) | r1_tsep_1(X2,X0) | ~r1_tsep_1(X2,k1_tsep_1(sK0,X0,X1))) ) | (~spl4_6 | ~spl4_41)),
% 4.70/0.97    inference(resolution,[],[f318,f120])).
% 4.70/0.97  fof(f318,plain,(
% 4.70/0.97    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | r1_tsep_1(X3,X1) | ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) ) | ~spl4_41),
% 4.70/0.97    inference(avatar_component_clause,[],[f317])).
% 4.70/0.97  fof(f467,plain,(
% 4.70/0.97    spl4_59 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_36),
% 4.70/0.97    inference(avatar_split_clause,[],[f303,f270,f119,f115,f111,f465])).
% 4.70/0.97  fof(f270,plain,(
% 4.70/0.97    spl4_36 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X2,X1) | m1_pre_topc(k2_tsep_1(X0,X2,X1),X1))),
% 4.70/0.97    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 4.70/0.97  fof(f303,plain,(
% 4.70/0.97    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~v1_tsep_1(X1,sK0) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(X1,X0) | m1_pre_topc(k2_tsep_1(sK0,X1,X0),X0)) ) | (spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_36)),
% 4.70/0.97    inference(subsumption_resolution,[],[f302,f112])).
% 4.70/0.97  fof(f302,plain,(
% 4.70/0.97    ( ! [X0,X1] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~v1_tsep_1(X1,sK0) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(X1,X0) | m1_pre_topc(k2_tsep_1(sK0,X1,X0),X0)) ) | (~spl4_5 | ~spl4_6 | ~spl4_36)),
% 4.70/0.97    inference(subsumption_resolution,[],[f300,f116])).
% 4.70/0.97  fof(f300,plain,(
% 4.70/0.97    ( ! [X0,X1] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~v1_tsep_1(X1,sK0) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(X1,X0) | m1_pre_topc(k2_tsep_1(sK0,X1,X0),X0)) ) | (~spl4_6 | ~spl4_36)),
% 4.70/0.97    inference(resolution,[],[f271,f120])).
% 4.70/0.97  fof(f271,plain,(
% 4.70/0.97    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X2,X1) | m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)) ) | ~spl4_36),
% 4.70/0.97    inference(avatar_component_clause,[],[f270])).
% 4.70/0.97  fof(f440,plain,(
% 4.70/0.97    spl4_56),
% 4.70/0.97    inference(avatar_split_clause,[],[f71,f438])).
% 4.70/0.97  fof(f71,plain,(
% 4.70/0.97    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X1,X2) | ~r1_tsep_1(X2,X3) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))) )),
% 4.70/0.97    inference(cnf_transformation,[],[f30])).
% 4.70/0.97  fof(f30,plain,(
% 4.70/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.70/0.97    inference(flattening,[],[f29])).
% 4.70/0.97  fof(f29,plain,(
% 4.70/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.70/0.97    inference(ennf_transformation,[],[f11])).
% 4.70/0.97  fof(f11,axiom,(
% 4.70/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 4.70/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tmap_1)).
% 4.70/0.97  fof(f319,plain,(
% 4.70/0.97    spl4_41),
% 4.70/0.97    inference(avatar_split_clause,[],[f63,f317])).
% 4.70/0.97  fof(f63,plain,(
% 4.70/0.97    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | r1_tsep_1(X3,X1) | ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) )),
% 4.70/0.97    inference(cnf_transformation,[],[f28])).
% 4.70/0.97  fof(f28,plain,(
% 4.70/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) | (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1) | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & (~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) | (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3) | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.70/0.97    inference(flattening,[],[f27])).
% 4.70/0.97  fof(f27,plain,(
% 4.70/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) | (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1) | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & (~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) | (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3) | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.70/0.97    inference(ennf_transformation,[],[f12])).
% 4.70/0.97  fof(f12,axiom,(
% 4.70/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~(r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & ~(r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & ~(r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1) & ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & ~(r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3) & ~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)))))))),
% 4.70/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tmap_1)).
% 4.70/0.97  fof(f295,plain,(
% 4.70/0.97    ~spl4_16 | spl4_2 | ~spl4_11 | spl4_14 | ~spl4_38),
% 4.70/0.97    inference(avatar_split_clause,[],[f292,f278,f151,f139,f103,f157])).
% 4.70/0.97  fof(f157,plain,(
% 4.70/0.97    spl4_16 <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))),
% 4.70/0.97    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 4.70/0.97  fof(f151,plain,(
% 4.70/0.97    spl4_14 <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))),
% 4.70/0.97    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 4.70/0.97  fof(f292,plain,(
% 4.70/0.97    ~m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) | (spl4_2 | ~spl4_11 | spl4_14 | ~spl4_38)),
% 4.70/0.97    inference(backward_demodulation,[],[f152,f291])).
% 4.70/0.97  fof(f152,plain,(
% 4.70/0.97    ~m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) | spl4_14),
% 4.70/0.97    inference(avatar_component_clause,[],[f151])).
% 4.70/0.97  fof(f280,plain,(
% 4.70/0.97    spl4_38 | spl4_3 | ~spl4_12 | ~spl4_34),
% 4.70/0.97    inference(avatar_split_clause,[],[f266,f253,f143,f107,f278])).
% 4.70/0.97  fof(f253,plain,(
% 4.70/0.97    spl4_34 <=> ! [X1,X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0))),
% 4.70/0.97    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 4.70/0.97  fof(f266,plain,(
% 4.70/0.97    ( ! [X3] : (v2_struct_0(X3) | ~m1_pre_topc(X3,sK0) | k1_tsep_1(sK0,sK1,X3) = k1_tsep_1(sK0,X3,sK1)) ) | (spl4_3 | ~spl4_12 | ~spl4_34)),
% 4.70/0.97    inference(subsumption_resolution,[],[f261,f108])).
% 4.70/0.97  fof(f261,plain,(
% 4.70/0.97    ( ! [X3] : (v2_struct_0(sK1) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK0) | k1_tsep_1(sK0,sK1,X3) = k1_tsep_1(sK0,X3,sK1)) ) | (~spl4_12 | ~spl4_34)),
% 4.70/0.97    inference(resolution,[],[f254,f144])).
% 4.70/0.97  fof(f254,plain,(
% 4.70/0.97    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0)) ) | ~spl4_34),
% 4.70/0.97    inference(avatar_component_clause,[],[f253])).
% 4.70/0.97  fof(f272,plain,(
% 4.70/0.97    spl4_36),
% 4.70/0.97    inference(avatar_split_clause,[],[f59,f270])).
% 4.70/0.97  fof(f59,plain,(
% 4.70/0.97    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X2,X1) | m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)) )),
% 4.70/0.97    inference(cnf_transformation,[],[f22])).
% 4.70/0.97  fof(f22,plain,(
% 4.70/0.97    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(k2_tsep_1(X0,X2,X1),X1) & v1_tsep_1(k2_tsep_1(X0,X2,X1),X1)) | r1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.70/0.97    inference(flattening,[],[f21])).
% 4.70/0.97  fof(f21,plain,(
% 4.70/0.97    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(k2_tsep_1(X0,X2,X1),X1) & v1_tsep_1(k2_tsep_1(X0,X2,X1),X1)) | r1_tsep_1(X2,X1)) | (~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.70/0.97    inference(ennf_transformation,[],[f13])).
% 4.70/0.97  fof(f13,axiom,(
% 4.70/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X2,X1) => (m1_pre_topc(k2_tsep_1(X0,X2,X1),X1) & v1_tsep_1(k2_tsep_1(X0,X2,X1),X1))))))),
% 4.70/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tmap_1)).
% 4.70/0.97  fof(f259,plain,(
% 4.70/0.97    spl4_35),
% 4.70/0.97    inference(avatar_split_clause,[],[f58,f257])).
% 4.70/0.97  fof(f58,plain,(
% 4.70/0.97    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X2,X1) | v1_tsep_1(k2_tsep_1(X0,X2,X1),X1)) )),
% 4.70/0.97    inference(cnf_transformation,[],[f22])).
% 4.70/0.97  fof(f255,plain,(
% 4.70/0.97    spl4_34 | spl4_4 | ~spl4_6 | ~spl4_28),
% 4.70/0.97    inference(avatar_split_clause,[],[f237,f208,f119,f111,f253])).
% 4.70/0.97  fof(f208,plain,(
% 4.70/0.97    spl4_28 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1))),
% 4.70/0.97    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 4.70/0.97  fof(f237,plain,(
% 4.70/0.97    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0)) ) | (spl4_4 | ~spl4_6 | ~spl4_28)),
% 4.70/0.97    inference(subsumption_resolution,[],[f235,f112])).
% 4.70/0.97  fof(f235,plain,(
% 4.70/0.97    ( ! [X0,X1] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0)) ) | (~spl4_6 | ~spl4_28)),
% 4.70/0.97    inference(resolution,[],[f209,f120])).
% 4.70/0.97  fof(f209,plain,(
% 4.70/0.97    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)) ) | ~spl4_28),
% 4.70/0.97    inference(avatar_component_clause,[],[f208])).
% 4.70/0.97  fof(f241,plain,(
% 4.70/0.97    spl4_31),
% 4.70/0.97    inference(avatar_split_clause,[],[f95,f239])).
% 4.70/0.97  fof(f95,plain,(
% 4.70/0.97    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | v1_tsep_1(X1,X0)) )),
% 4.70/0.97    inference(subsumption_resolution,[],[f94,f74])).
% 4.70/0.97  fof(f74,plain,(
% 4.70/0.97    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 4.70/0.97    inference(cnf_transformation,[],[f34])).
% 4.70/0.97  fof(f34,plain,(
% 4.70/0.97    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.70/0.97    inference(flattening,[],[f33])).
% 4.70/0.97  fof(f33,plain,(
% 4.70/0.97    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.70/0.97    inference(ennf_transformation,[],[f1])).
% 4.70/0.97  fof(f1,axiom,(
% 4.70/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 4.70/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 4.70/0.97  fof(f94,plain,(
% 4.70/0.97    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | v1_tsep_1(X1,X0)) )),
% 4.70/0.97    inference(subsumption_resolution,[],[f88,f56])).
% 4.70/0.97  fof(f56,plain,(
% 4.70/0.97    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 4.70/0.97    inference(cnf_transformation,[],[f18])).
% 4.70/0.97  fof(f18,plain,(
% 4.70/0.97    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.70/0.97    inference(ennf_transformation,[],[f2])).
% 4.70/0.97  fof(f2,axiom,(
% 4.70/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 4.70/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 4.70/0.97  fof(f88,plain,(
% 4.70/0.97    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | v1_tsep_1(X1,X0)) )),
% 4.70/0.97    inference(equality_resolution,[],[f76])).
% 4.70/0.97  fof(f76,plain,(
% 4.70/0.97    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 4.70/0.97    inference(cnf_transformation,[],[f36])).
% 4.70/0.97  fof(f36,plain,(
% 4.70/0.97    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.70/0.97    inference(flattening,[],[f35])).
% 4.70/0.97  fof(f35,plain,(
% 4.70/0.97    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.70/0.97    inference(ennf_transformation,[],[f6])).
% 4.70/0.97  fof(f6,axiom,(
% 4.70/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 4.70/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tmap_1)).
% 4.70/0.97  fof(f221,plain,(
% 4.70/0.97    spl4_2 | spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_11 | ~spl4_12 | spl4_16 | ~spl4_24),
% 4.70/0.97    inference(avatar_contradiction_clause,[],[f220])).
% 4.70/0.97  fof(f220,plain,(
% 4.70/0.97    $false | (spl4_2 | spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_11 | ~spl4_12 | spl4_16 | ~spl4_24)),
% 4.70/0.97    inference(subsumption_resolution,[],[f219,f112])).
% 4.70/0.97  fof(f219,plain,(
% 4.70/0.97    v2_struct_0(sK0) | (spl4_2 | spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_11 | ~spl4_12 | spl4_16 | ~spl4_24)),
% 4.70/0.97    inference(subsumption_resolution,[],[f218,f140])).
% 4.70/0.97  fof(f218,plain,(
% 4.70/0.97    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl4_2 | spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_12 | spl4_16 | ~spl4_24)),
% 4.70/0.97    inference(subsumption_resolution,[],[f217,f104])).
% 4.70/0.97  fof(f217,plain,(
% 4.70/0.97    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_12 | spl4_16 | ~spl4_24)),
% 4.70/0.97    inference(subsumption_resolution,[],[f216,f144])).
% 4.70/0.97  fof(f216,plain,(
% 4.70/0.97    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl4_3 | ~spl4_5 | ~spl4_6 | spl4_16 | ~spl4_24)),
% 4.70/0.97    inference(subsumption_resolution,[],[f215,f108])).
% 4.70/0.97  fof(f215,plain,(
% 4.70/0.97    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl4_5 | ~spl4_6 | spl4_16 | ~spl4_24)),
% 4.70/0.97    inference(subsumption_resolution,[],[f214,f120])).
% 4.70/0.97  fof(f214,plain,(
% 4.70/0.97    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl4_5 | spl4_16 | ~spl4_24)),
% 4.70/0.97    inference(subsumption_resolution,[],[f212,f116])).
% 4.70/0.97  fof(f212,plain,(
% 4.70/0.97    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl4_16 | ~spl4_24)),
% 4.70/0.97    inference(resolution,[],[f189,f158])).
% 4.70/0.97  fof(f158,plain,(
% 4.70/0.97    ~m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) | spl4_16),
% 4.70/0.97    inference(avatar_component_clause,[],[f157])).
% 4.70/0.97  fof(f189,plain,(
% 4.70/0.97    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) ) | ~spl4_24),
% 4.70/0.97    inference(avatar_component_clause,[],[f188])).
% 4.70/0.97  fof(f188,plain,(
% 4.70/0.97    spl4_24 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))),
% 4.70/0.97    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 4.70/0.97  fof(f210,plain,(
% 4.70/0.97    spl4_28),
% 4.70/0.97    inference(avatar_split_clause,[],[f79,f208])).
% 4.70/0.97  fof(f79,plain,(
% 4.70/0.97    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)) )),
% 4.70/0.97    inference(cnf_transformation,[],[f38])).
% 4.70/0.97  fof(f38,plain,(
% 4.70/0.97    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 4.70/0.97    inference(flattening,[],[f37])).
% 4.70/0.97  fof(f37,plain,(
% 4.70/0.97    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 4.70/0.97    inference(ennf_transformation,[],[f3])).
% 4.70/0.97  fof(f3,axiom,(
% 4.70/0.97    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1))),
% 4.70/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).
% 4.70/0.97  fof(f206,plain,(
% 4.70/0.97    spl4_27 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_22),
% 4.70/0.97    inference(avatar_split_clause,[],[f202,f180,f119,f115,f111,f204])).
% 4.70/0.97  fof(f202,plain,(
% 4.70/0.97    ( ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0)) ) | (spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_22)),
% 4.70/0.97    inference(subsumption_resolution,[],[f201,f112])).
% 4.70/0.97  fof(f201,plain,(
% 4.70/0.97    ( ! [X0] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0)) ) | (~spl4_5 | ~spl4_6 | ~spl4_22)),
% 4.70/0.97    inference(subsumption_resolution,[],[f199,f116])).
% 4.70/0.97  fof(f199,plain,(
% 4.70/0.97    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(sK0,X0,X0)) ) | (~spl4_6 | ~spl4_22)),
% 4.70/0.97    inference(resolution,[],[f181,f120])).
% 4.70/0.97  fof(f198,plain,(
% 4.70/0.97    spl4_26),
% 4.70/0.97    inference(avatar_split_clause,[],[f62,f196])).
% 4.70/0.97  fof(f62,plain,(
% 4.70/0.97    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | ~r1_tsep_1(X2,X1)) )),
% 4.70/0.97    inference(cnf_transformation,[],[f26])).
% 4.70/0.97  fof(f26,plain,(
% 4.70/0.97    ! [X0] : (! [X1] : (! [X2] : ((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.70/0.97    inference(flattening,[],[f25])).
% 4.70/0.97  fof(f25,plain,(
% 4.70/0.97    ! [X0] : (! [X1] : (! [X2] : (((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.70/0.97    inference(ennf_transformation,[],[f7])).
% 4.70/0.97  fof(f7,axiom,(
% 4.70/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 4.70/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).
% 4.70/0.97  fof(f190,plain,(
% 4.70/0.97    spl4_24),
% 4.70/0.97    inference(avatar_split_clause,[],[f60,f188])).
% 4.70/0.97  fof(f60,plain,(
% 4.70/0.97    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))) )),
% 4.70/0.97    inference(cnf_transformation,[],[f24])).
% 4.70/0.97  fof(f24,plain,(
% 4.70/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.70/0.97    inference(flattening,[],[f23])).
% 4.70/0.97  fof(f23,plain,(
% 4.70/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.70/0.97    inference(ennf_transformation,[],[f8])).
% 4.70/0.97  fof(f8,axiom,(
% 4.70/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 4.70/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).
% 4.70/0.97  fof(f186,plain,(
% 4.70/0.97    spl4_23),
% 4.70/0.97    inference(avatar_split_clause,[],[f85,f184])).
% 4.70/0.97  fof(f85,plain,(
% 4.70/0.97    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_pre_topc(k1_tsep_1(X0,X1,X2))) )),
% 4.70/0.97    inference(cnf_transformation,[],[f42])).
% 4.70/0.97  fof(f42,plain,(
% 4.70/0.97    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.70/0.97    inference(flattening,[],[f41])).
% 4.70/0.97  fof(f41,plain,(
% 4.70/0.97    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.70/0.97    inference(ennf_transformation,[],[f5])).
% 4.70/0.97  fof(f5,axiom,(
% 4.70/0.97    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 4.70/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tmap_1)).
% 4.70/0.97  fof(f182,plain,(
% 4.70/0.97    spl4_22),
% 4.70/0.97    inference(avatar_split_clause,[],[f57,f180])).
% 4.70/0.97  fof(f57,plain,(
% 4.70/0.97    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)) )),
% 4.70/0.97    inference(cnf_transformation,[],[f20])).
% 4.70/0.97  fof(f20,plain,(
% 4.70/0.97    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.70/0.97    inference(flattening,[],[f19])).
% 4.70/0.97  fof(f19,plain,(
% 4.70/0.97    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.70/0.97    inference(ennf_transformation,[],[f9])).
% 4.70/0.97  fof(f9,axiom,(
% 4.70/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 4.70/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).
% 4.70/0.97  fof(f178,plain,(
% 4.70/0.97    spl4_21),
% 4.70/0.97    inference(avatar_split_clause,[],[f82,f176])).
% 4.70/0.97  fof(f82,plain,(
% 4.70/0.97    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)) )),
% 4.70/0.97    inference(cnf_transformation,[],[f40])).
% 4.70/0.97  fof(f40,plain,(
% 4.70/0.97    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 4.70/0.97    inference(flattening,[],[f39])).
% 4.70/0.97  fof(f39,plain,(
% 4.70/0.97    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 4.70/0.97    inference(ennf_transformation,[],[f4])).
% 4.70/0.97  fof(f4,axiom,(
% 4.70/0.97    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 4.70/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 4.70/0.97  fof(f170,plain,(
% 4.70/0.97    spl4_19),
% 4.70/0.97    inference(avatar_split_clause,[],[f80,f168])).
% 4.70/0.97  fof(f80,plain,(
% 4.70/0.97    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~v2_struct_0(k1_tsep_1(X0,X1,X2))) )),
% 4.70/0.97    inference(cnf_transformation,[],[f40])).
% 4.70/0.97  fof(f166,plain,(
% 4.70/0.97    spl4_18),
% 4.70/0.97    inference(avatar_split_clause,[],[f74,f164])).
% 4.70/0.97  fof(f162,plain,(
% 4.70/0.97    ~spl4_14 | ~spl4_15 | ~spl4_16 | ~spl4_17),
% 4.70/0.97    inference(avatar_split_clause,[],[f43,f160,f157,f154,f151])).
% 4.70/0.97  fof(f43,plain,(
% 4.70/0.97    ~v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) | ~v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1)) | ~m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))),
% 4.70/0.97    inference(cnf_transformation,[],[f17])).
% 4.70/0.97  fof(f17,plain,(
% 4.70/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(X1,k1_tsep_1(X0,X2,X1)) | ~v1_tsep_1(X1,k1_tsep_1(X0,X2,X1)) | ~m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~v1_tsep_1(X1,k1_tsep_1(X0,X1,X2))) & r1_tsep_1(X3,X2) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.70/0.97    inference(flattening,[],[f16])).
% 4.70/0.97  fof(f16,plain,(
% 4.70/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(X1,k1_tsep_1(X0,X2,X1)) | ~v1_tsep_1(X1,k1_tsep_1(X0,X2,X1)) | ~m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~v1_tsep_1(X1,k1_tsep_1(X0,X1,X2))) & (r1_tsep_1(X3,X2) & m1_pre_topc(X1,X3))) & (m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 4.70/0.97    inference(ennf_transformation,[],[f15])).
% 4.70/0.97  fof(f15,negated_conjecture,(
% 4.70/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => ((r1_tsep_1(X3,X2) & m1_pre_topc(X1,X3)) => (m1_pre_topc(X1,k1_tsep_1(X0,X2,X1)) & v1_tsep_1(X1,k1_tsep_1(X0,X2,X1)) & m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) & v1_tsep_1(X1,k1_tsep_1(X0,X1,X2))))))))),
% 4.70/0.97    inference(negated_conjecture,[],[f14])).
% 4.70/0.97  fof(f14,conjecture,(
% 4.70/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => ((r1_tsep_1(X3,X2) & m1_pre_topc(X1,X3)) => (m1_pre_topc(X1,k1_tsep_1(X0,X2,X1)) & v1_tsep_1(X1,k1_tsep_1(X0,X2,X1)) & m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) & v1_tsep_1(X1,k1_tsep_1(X0,X1,X2))))))))),
% 4.70/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tmap_1)).
% 4.70/0.97  fof(f149,plain,(
% 4.70/0.97    spl4_13),
% 4.70/0.97    inference(avatar_split_clause,[],[f56,f147])).
% 4.70/0.97  fof(f145,plain,(
% 4.70/0.97    spl4_12),
% 4.70/0.97    inference(avatar_split_clause,[],[f52,f143])).
% 4.70/0.97  fof(f52,plain,(
% 4.70/0.97    m1_pre_topc(sK1,sK0)),
% 4.70/0.97    inference(cnf_transformation,[],[f17])).
% 4.70/0.97  fof(f141,plain,(
% 4.70/0.97    spl4_11),
% 4.70/0.97    inference(avatar_split_clause,[],[f50,f139])).
% 4.70/0.97  fof(f50,plain,(
% 4.70/0.97    m1_pre_topc(sK2,sK0)),
% 4.70/0.97    inference(cnf_transformation,[],[f17])).
% 4.70/0.97  fof(f137,plain,(
% 4.70/0.97    spl4_10),
% 4.70/0.97    inference(avatar_split_clause,[],[f48,f135])).
% 4.70/0.97  fof(f48,plain,(
% 4.70/0.97    r1_tsep_1(sK3,sK2)),
% 4.70/0.97    inference(cnf_transformation,[],[f17])).
% 4.70/0.97  fof(f133,plain,(
% 4.70/0.97    spl4_9),
% 4.70/0.97    inference(avatar_split_clause,[],[f47,f131])).
% 4.70/0.97  fof(f47,plain,(
% 4.70/0.97    m1_pre_topc(sK1,sK3)),
% 4.70/0.97    inference(cnf_transformation,[],[f17])).
% 4.70/0.97  fof(f129,plain,(
% 4.70/0.97    spl4_8),
% 4.70/0.97    inference(avatar_split_clause,[],[f46,f127])).
% 4.70/0.97  fof(f46,plain,(
% 4.70/0.97    m1_pre_topc(sK3,sK0)),
% 4.70/0.97    inference(cnf_transformation,[],[f17])).
% 4.70/0.97  fof(f125,plain,(
% 4.70/0.97    spl4_7),
% 4.70/0.97    inference(avatar_split_clause,[],[f45,f123])).
% 4.70/0.97  fof(f45,plain,(
% 4.70/0.97    v1_tsep_1(sK3,sK0)),
% 4.70/0.97    inference(cnf_transformation,[],[f17])).
% 4.70/0.97  fof(f121,plain,(
% 4.70/0.97    spl4_6),
% 4.70/0.97    inference(avatar_split_clause,[],[f55,f119])).
% 4.70/0.97  fof(f55,plain,(
% 4.70/0.97    l1_pre_topc(sK0)),
% 4.70/0.97    inference(cnf_transformation,[],[f17])).
% 4.70/0.97  fof(f117,plain,(
% 4.70/0.97    spl4_5),
% 4.70/0.97    inference(avatar_split_clause,[],[f54,f115])).
% 4.70/0.97  fof(f54,plain,(
% 4.70/0.97    v2_pre_topc(sK0)),
% 4.70/0.97    inference(cnf_transformation,[],[f17])).
% 4.70/0.97  fof(f113,plain,(
% 4.70/0.97    ~spl4_4),
% 4.70/0.97    inference(avatar_split_clause,[],[f53,f111])).
% 4.70/0.97  fof(f53,plain,(
% 4.70/0.97    ~v2_struct_0(sK0)),
% 4.70/0.97    inference(cnf_transformation,[],[f17])).
% 4.70/0.97  fof(f109,plain,(
% 4.70/0.97    ~spl4_3),
% 4.70/0.97    inference(avatar_split_clause,[],[f51,f107])).
% 4.70/0.97  fof(f51,plain,(
% 4.70/0.97    ~v2_struct_0(sK1)),
% 4.70/0.97    inference(cnf_transformation,[],[f17])).
% 4.70/0.97  fof(f105,plain,(
% 4.70/0.97    ~spl4_2),
% 4.70/0.97    inference(avatar_split_clause,[],[f49,f103])).
% 4.70/0.97  fof(f49,plain,(
% 4.70/0.97    ~v2_struct_0(sK2)),
% 4.70/0.97    inference(cnf_transformation,[],[f17])).
% 4.70/0.97  fof(f101,plain,(
% 4.70/0.97    ~spl4_1),
% 4.70/0.97    inference(avatar_split_clause,[],[f44,f99])).
% 4.70/0.97  fof(f44,plain,(
% 4.70/0.97    ~v2_struct_0(sK3)),
% 4.70/0.97    inference(cnf_transformation,[],[f17])).
% 4.70/0.97  % SZS output end Proof for theBenchmark
% 4.70/0.97  % (12329)------------------------------
% 4.70/0.97  % (12329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.70/0.97  % (12329)Termination reason: Refutation
% 4.70/0.97  
% 4.70/0.97  % (12329)Memory used [KB]: 15607
% 4.70/0.97  % (12329)Time elapsed: 0.544 s
% 4.70/0.97  % (12329)------------------------------
% 4.70/0.97  % (12329)------------------------------
% 4.70/0.97  % (12319)Success in time 0.614 s
%------------------------------------------------------------------------------
