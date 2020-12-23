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
% DateTime   : Thu Dec  3 13:09:28 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  374 (1014 expanded)
%              Number of leaves         :   93 ( 431 expanded)
%              Depth                    :   19
%              Number of atoms          : 1666 (6221 expanded)
%              Number of equality atoms :  113 ( 624 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (8481)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
fof(f4602,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f142,f147,f152,f157,f163,f168,f173,f178,f184,f189,f194,f203,f204,f212,f227,f232,f252,f257,f293,f362,f370,f384,f394,f562,f596,f661,f727,f758,f816,f845,f1106,f1115,f1129,f1364,f1393,f1397,f1402,f1408,f1615,f1731,f1752,f1755,f1758,f1787,f2207,f2211,f2291,f2297,f2567,f2568,f2594,f2601,f2602,f2646,f3493,f3508,f3520,f3528,f3536,f3815,f3914,f3917,f4018,f4032,f4587,f4588,f4589,f4590,f4601])).

fof(f4601,plain,
    ( ~ spl6_119
    | ~ spl6_35
    | ~ spl6_70
    | spl6_85 ),
    inference(avatar_split_clause,[],[f4600,f1745,f1361,f559,f2560])).

fof(f2560,plain,
    ( spl6_119
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_119])])).

fof(f559,plain,
    ( spl6_35
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f1361,plain,
    ( spl6_70
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f1745,plain,
    ( spl6_85
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f4600,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_35
    | ~ spl6_70
    | spl6_85 ),
    inference(forward_demodulation,[],[f4599,f561])).

fof(f561,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f559])).

fof(f4599,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_70
    | spl6_85 ),
    inference(forward_demodulation,[],[f4598,f129])).

fof(f129,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f4598,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl6_70
    | spl6_85 ),
    inference(forward_demodulation,[],[f1747,f1363])).

fof(f1363,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_70 ),
    inference(avatar_component_clause,[],[f1361])).

fof(f1747,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl6_85 ),
    inference(avatar_component_clause,[],[f1745])).

fof(f4590,plain,
    ( k1_xboole_0 != sK3
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4589,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4588,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != u1_struct_0(sK0)
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4587,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_42
    | ~ spl6_161
    | ~ spl6_179
    | spl6_118
    | ~ spl6_129
    | ~ spl6_165 ),
    inference(avatar_split_clause,[],[f4582,f3506,f2643,f2556,f4584,f3477,f696,f144,f139])).

fof(f139,plain,
    ( spl6_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f144,plain,
    ( spl6_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f696,plain,
    ( spl6_42
  <=> v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f3477,plain,
    ( spl6_161
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_161])])).

fof(f4584,plain,
    ( spl6_179
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_179])])).

fof(f2556,plain,
    ( spl6_118
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).

fof(f2643,plain,
    ( spl6_129
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_129])])).

fof(f3506,plain,
    ( spl6_165
  <=> ! [X2] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X2),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(k1_xboole_0,X2,sK1)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X2),u1_struct_0(sK1))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_165])])).

fof(f4582,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_118
    | ~ spl6_129
    | ~ spl6_165 ),
    inference(forward_demodulation,[],[f4581,f2645])).

fof(f2645,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl6_129 ),
    inference(avatar_component_clause,[],[f2643])).

fof(f4581,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_118
    | ~ spl6_129
    | ~ spl6_165 ),
    inference(forward_demodulation,[],[f3800,f2645])).

fof(f3800,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_118
    | ~ spl6_165 ),
    inference(resolution,[],[f2557,f3509])).

fof(f3509,plain,
    ( ! [X0] :
        ( v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl6_165 ),
    inference(resolution,[],[f3507,f107])).

fof(f107,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f3507,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
        | v5_pre_topc(k1_xboole_0,X2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(k1_xboole_0,X2,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X2),k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X2),u1_struct_0(sK1))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2) )
    | ~ spl6_165 ),
    inference(avatar_component_clause,[],[f3506])).

fof(f2557,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_118 ),
    inference(avatar_component_clause,[],[f2556])).

fof(f4032,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_12
    | ~ spl6_73
    | ~ spl6_74
    | spl6_75 ),
    inference(avatar_contradiction_clause,[],[f4020])).

fof(f4020,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_12
    | ~ spl6_73
    | ~ spl6_74
    | spl6_75 ),
    inference(unit_resulting_resolution,[],[f141,f146,f151,f156,f161,f197,f172,f177,f1392,f1383,f1387,f136])).

fof(f136,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f1387,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f1386])).

fof(f1386,plain,
    ( spl6_74
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f1383,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl6_73 ),
    inference(avatar_component_clause,[],[f1382])).

fof(f1382,plain,
    ( spl6_73
  <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f1392,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl6_75 ),
    inference(avatar_component_clause,[],[f1390])).

fof(f1390,plain,
    ( spl6_75
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f177,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl6_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f172,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl6_7
  <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f197,plain,
    ( v5_pre_topc(sK3,sK0,sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl6_12
  <=> v5_pre_topc(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f161,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl6_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f156,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f151,plain,
    ( v2_pre_topc(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl6_3
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f146,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f144])).

fof(f141,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f139])).

fof(f4018,plain,
    ( ~ spl6_8
    | ~ spl6_18
    | ~ spl6_64
    | ~ spl6_69
    | spl6_74 ),
    inference(avatar_contradiction_clause,[],[f4004])).

fof(f4004,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_18
    | ~ spl6_64
    | ~ spl6_69
    | spl6_74 ),
    inference(unit_resulting_resolution,[],[f1359,f256,f1388,f3833])).

fof(f3833,plain,
    ( ! [X1] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
        | ~ v4_relat_1(sK3,X1)
        | ~ v1_partfun1(sK3,X1) )
    | ~ spl6_8
    | ~ spl6_64 ),
    inference(superposition,[],[f177,f1128])).

fof(f1128,plain,
    ( ! [X5] :
        ( u1_struct_0(sK0) = X5
        | ~ v4_relat_1(sK3,X5)
        | ~ v1_partfun1(sK3,X5) )
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f1127])).

fof(f1127,plain,
    ( spl6_64
  <=> ! [X5] :
        ( u1_struct_0(sK0) = X5
        | ~ v4_relat_1(sK3,X5)
        | ~ v1_partfun1(sK3,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f1388,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | spl6_74 ),
    inference(avatar_component_clause,[],[f1386])).

fof(f256,plain,
    ( v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl6_18
  <=> v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f1359,plain,
    ( v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl6_69 ),
    inference(avatar_component_clause,[],[f1357])).

fof(f1357,plain,
    ( spl6_69
  <=> v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f3917,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_71
    | ~ spl6_72
    | ~ spl6_73
    | ~ spl6_74
    | spl6_75 ),
    inference(avatar_contradiction_clause,[],[f3915])).

fof(f3915,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_71
    | ~ spl6_72
    | ~ spl6_73
    | ~ spl6_74
    | spl6_75 ),
    inference(unit_resulting_resolution,[],[f156,f161,f151,f1375,f1379,f1383,f1387,f201,f188,f193,f1392,f135])).

fof(f135,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f193,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl6_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f188,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl6_10
  <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f201,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl6_13
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f1379,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_72 ),
    inference(avatar_component_clause,[],[f1378])).

fof(f1378,plain,
    ( spl6_72
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f1375,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_71 ),
    inference(avatar_component_clause,[],[f1374])).

fof(f1374,plain,
    ( spl6_71
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f3914,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | spl6_12
    | ~ spl6_73
    | ~ spl6_74
    | ~ spl6_75 ),
    inference(avatar_contradiction_clause,[],[f3902])).

fof(f3902,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | spl6_12
    | ~ spl6_73
    | ~ spl6_74
    | ~ spl6_75 ),
    inference(unit_resulting_resolution,[],[f141,f146,f151,f156,f161,f198,f172,f177,f1391,f1383,f1387,f137])).

fof(f137,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1391,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_75 ),
    inference(avatar_component_clause,[],[f1390])).

fof(f198,plain,
    ( ~ v5_pre_topc(sK3,sK0,sK1)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f196])).

fof(f3815,plain,(
    spl6_120 ),
    inference(avatar_contradiction_clause,[],[f3808])).

fof(f3808,plain,
    ( $false
    | spl6_120 ),
    inference(unit_resulting_resolution,[],[f308,f2566])).

fof(f2566,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | spl6_120 ),
    inference(avatar_component_clause,[],[f2564])).

fof(f2564,plain,
    ( spl6_120
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).

fof(f308,plain,(
    ! [X4] : v1_funct_2(k1_xboole_0,X4,k1_xboole_0) ),
    inference(superposition,[],[f101,f303])).

fof(f303,plain,(
    ! [X0] : k1_xboole_0 = sK4(X0,k1_xboole_0) ),
    inference(resolution,[],[f279,f116])).

fof(f116,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f50,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f279,plain,(
    ! [X12,X13] : ~ r2_hidden(X12,sK4(X13,k1_xboole_0)) ),
    inference(global_subsumption,[],[f108,f277])).

fof(f277,plain,(
    ! [X12,X13] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(X12,sK4(X13,k1_xboole_0)) ) ),
    inference(resolution,[],[f112,f213])).

fof(f213,plain,(
    ! [X0] : m1_subset_1(sK4(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f96,f129])).

fof(f96,plain,(
    ! [X0,X1] : m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK4(X0,X1),X0,X1)
      & v1_funct_1(sK4(X0,X1))
      & v5_relat_1(sK4(X0,X1),X1)
      & v4_relat_1(sK4(X0,X1),X0)
      & v1_relat_1(sK4(X0,X1))
      & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK4(X0,X1),X0,X1)
        & v1_funct_1(sK4(X0,X1))
        & v5_relat_1(sK4(X0,X1),X1)
        & v4_relat_1(sK4(X0,X1),X0)
        & v1_relat_1(sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f108,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f101,plain,(
    ! [X0,X1] : v1_funct_2(sK4(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f63])).

fof(f3536,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != u1_struct_0(sK1)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3528,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_42
    | ~ spl6_49
    | ~ spl6_118
    | ~ spl6_166 ),
    inference(avatar_contradiction_clause,[],[f3521])).

fof(f3521,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_42
    | ~ spl6_49
    | ~ spl6_118
    | ~ spl6_166 ),
    inference(unit_resulting_resolution,[],[f141,f146,f697,f308,f844,f107,f2558,f3519])).

fof(f3519,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl6_166 ),
    inference(avatar_component_clause,[],[f3518])).

fof(f3518,plain,
    ( spl6_166
  <=> ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_166])])).

fof(f2558,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_118 ),
    inference(avatar_component_clause,[],[f2556])).

fof(f844,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f842])).

fof(f842,plain,
    ( spl6_49
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f697,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl6_42 ),
    inference(avatar_component_clause,[],[f696])).

fof(f3520,plain,
    ( ~ spl6_4
    | ~ spl6_3
    | spl6_166
    | ~ spl6_70
    | ~ spl6_124 ),
    inference(avatar_split_clause,[],[f2614,f2592,f1361,f3518,f149,f154])).

fof(f2592,plain,
    ( spl6_124
  <=> ! [X1,X0] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | v5_pre_topc(k1_xboole_0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_124])])).

fof(f2614,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(k1_xboole_0,X0,sK1) )
    | ~ spl6_70
    | ~ spl6_124 ),
    inference(superposition,[],[f2593,f1363])).

fof(f2593,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(k1_xboole_0,X0,X1) )
    | ~ spl6_124 ),
    inference(avatar_component_clause,[],[f2592])).

fof(f3508,plain,
    ( ~ spl6_4
    | ~ spl6_3
    | spl6_165
    | ~ spl6_70
    | ~ spl6_89 ),
    inference(avatar_split_clause,[],[f2419,f1785,f1361,f3506,f149,f154])).

fof(f1785,plain,
    ( spl6_89
  <=> ! [X1,X0] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).

fof(f2419,plain,
    ( ! [X2] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X2),k1_xboole_0)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X2),u1_struct_0(sK1))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k1_xboole_0,X2,sK1)
        | v5_pre_topc(k1_xboole_0,X2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl6_70
    | ~ spl6_89 ),
    inference(superposition,[],[f1786,f1363])).

fof(f1786,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
    | ~ spl6_89 ),
    inference(avatar_component_clause,[],[f1785])).

fof(f3493,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | k1_xboole_0 != sK3
    | k1_xboole_0 != u1_struct_0(sK0)
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2646,plain,
    ( ~ spl6_62
    | spl6_129
    | ~ spl6_45
    | ~ spl6_125 ),
    inference(avatar_split_clause,[],[f2605,f2599,f755,f2643,f1100])).

fof(f1100,plain,
    ( spl6_62
  <=> v4_relat_1(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f755,plain,
    ( spl6_45
  <=> v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f2599,plain,
    ( spl6_125
  <=> ! [X1] :
        ( k1_xboole_0 = X1
        | ~ v1_partfun1(k1_xboole_0,X1)
        | ~ v4_relat_1(k1_xboole_0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_125])])).

fof(f2605,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ v4_relat_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl6_45
    | ~ spl6_125 ),
    inference(resolution,[],[f2600,f757])).

fof(f757,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f755])).

fof(f2600,plain,
    ( ! [X1] :
        ( ~ v1_partfun1(k1_xboole_0,X1)
        | k1_xboole_0 = X1
        | ~ v4_relat_1(k1_xboole_0,X1) )
    | ~ spl6_125 ),
    inference(avatar_component_clause,[],[f2599])).

fof(f2602,plain,
    ( k1_xboole_0 != sK3
    | v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v4_relat_1(sK3,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2601,plain,
    ( spl6_125
    | ~ spl6_53
    | ~ spl6_28
    | ~ spl6_63 ),
    inference(avatar_split_clause,[],[f2596,f1104,f381,f866,f2599])).

fof(f866,plain,
    ( spl6_53
  <=> v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f381,plain,
    ( spl6_28
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f1104,plain,
    ( spl6_63
  <=> ! [X4] :
        ( u1_struct_0(sK0) = X4
        | ~ v4_relat_1(k1_xboole_0,X4)
        | ~ v1_partfun1(k1_xboole_0,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f2596,plain,
    ( ! [X1] :
        ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
        | k1_xboole_0 = X1
        | ~ v4_relat_1(k1_xboole_0,X1)
        | ~ v1_partfun1(k1_xboole_0,X1) )
    | ~ spl6_28
    | ~ spl6_63 ),
    inference(resolution,[],[f2076,f383])).

fof(f383,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f381])).

fof(f2076,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(k1_xboole_0,X1)
        | ~ v4_relat_1(k1_xboole_0,X1)
        | X0 = X1
        | ~ v4_relat_1(k1_xboole_0,X0)
        | ~ v1_partfun1(k1_xboole_0,X0) )
    | ~ spl6_63 ),
    inference(superposition,[],[f1105,f1105])).

fof(f1105,plain,
    ( ! [X4] :
        ( u1_struct_0(sK0) = X4
        | ~ v4_relat_1(k1_xboole_0,X4)
        | ~ v1_partfun1(k1_xboole_0,X4) )
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f1104])).

fof(f2594,plain,
    ( ~ spl6_9
    | spl6_124 ),
    inference(avatar_split_clause,[],[f535,f2592,f181])).

fof(f181,plain,
    ( spl6_9
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f535,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(k1_xboole_0,X0,X1)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f135,f107])).

fof(f2568,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2567,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_82
    | ~ spl6_83
    | ~ spl6_47
    | spl6_118
    | ~ spl6_9
    | ~ spl6_98
    | ~ spl6_119
    | ~ spl6_120
    | ~ spl6_11
    | ~ spl6_35
    | ~ spl6_70 ),
    inference(avatar_split_clause,[],[f2541,f1361,f559,f191,f2564,f2560,f2195,f181,f2556,f828,f1737,f1733,f144,f139])).

fof(f1733,plain,
    ( spl6_82
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f1737,plain,
    ( spl6_83
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f828,plain,
    ( spl6_47
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f2195,plain,
    ( spl6_98
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f2541,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_11
    | ~ spl6_35
    | ~ spl6_70 ),
    inference(forward_demodulation,[],[f2540,f1363])).

fof(f2540,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_11
    | ~ spl6_35
    | ~ spl6_70 ),
    inference(forward_demodulation,[],[f2539,f129])).

fof(f2539,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_11
    | ~ spl6_35
    | ~ spl6_70 ),
    inference(forward_demodulation,[],[f2538,f1363])).

fof(f2538,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_11
    | ~ spl6_35
    | ~ spl6_70 ),
    inference(forward_demodulation,[],[f2394,f1363])).

fof(f2394,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_11
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f2393,f561])).

fof(f2393,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_11
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f2392,f561])).

fof(f2392,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_11
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f2391,f561])).

fof(f2391,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_11
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f2390,f561])).

fof(f2390,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_11
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f2389,f561])).

fof(f2389,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_11
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f549,f561])).

fof(f549,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_11 ),
    inference(resolution,[],[f137,f193])).

fof(f2297,plain,(
    spl6_101 ),
    inference(avatar_contradiction_clause,[],[f2292])).

fof(f2292,plain,
    ( $false
    | spl6_101 ),
    inference(unit_resulting_resolution,[],[f107,f2290])).

fof(f2290,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | spl6_101 ),
    inference(avatar_component_clause,[],[f2288])).

fof(f2288,plain,
    ( spl6_101
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).

fof(f2291,plain,
    ( ~ spl6_101
    | ~ spl6_35
    | spl6_74 ),
    inference(avatar_split_clause,[],[f2214,f1386,f559,f2288])).

fof(f2214,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl6_35
    | spl6_74 ),
    inference(forward_demodulation,[],[f1388,f561])).

fof(f2211,plain,
    ( k1_xboole_0 != sK3
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2207,plain,(
    spl6_98 ),
    inference(avatar_contradiction_clause,[],[f2199])).

fof(f2199,plain,
    ( $false
    | spl6_98 ),
    inference(unit_resulting_resolution,[],[f308,f2197])).

fof(f2197,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | spl6_98 ),
    inference(avatar_component_clause,[],[f2195])).

fof(f1787,plain,
    ( ~ spl6_9
    | spl6_89 ),
    inference(avatar_split_clause,[],[f529,f1785,f181])).

fof(f529,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
      | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f134,f107])).

fof(f134,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1758,plain,
    ( ~ spl6_4
    | spl6_83 ),
    inference(avatar_contradiction_clause,[],[f1756])).

fof(f1756,plain,
    ( $false
    | ~ spl6_4
    | spl6_83 ),
    inference(unit_resulting_resolution,[],[f156,f1739,f239])).

fof(f239,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f93,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f1739,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_83 ),
    inference(avatar_component_clause,[],[f1737])).

fof(f1755,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | spl6_82 ),
    inference(avatar_contradiction_clause,[],[f1753])).

fof(f1753,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_4
    | spl6_82 ),
    inference(unit_resulting_resolution,[],[f151,f156,f1735,f92])).

fof(f92,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f1735,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_82 ),
    inference(avatar_component_clause,[],[f1733])).

fof(f1752,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_82
    | ~ spl6_83
    | ~ spl6_84
    | ~ spl6_85
    | ~ spl6_5
    | ~ spl6_10
    | spl6_13
    | ~ spl6_86
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f542,f191,f1749,f200,f186,f159,f1745,f1741,f1737,f1733,f144,f139])).

fof(f1741,plain,
    ( spl6_84
  <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f1749,plain,
    ( spl6_86
  <=> v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f542,plain,
    ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_11 ),
    inference(resolution,[],[f136,f193])).

fof(f1731,plain,
    ( ~ spl6_17
    | ~ spl6_28
    | ~ spl6_63
    | spl6_68 ),
    inference(avatar_contradiction_clause,[],[f1727])).

fof(f1727,plain,
    ( $false
    | ~ spl6_17
    | ~ spl6_28
    | ~ spl6_63
    | spl6_68 ),
    inference(unit_resulting_resolution,[],[f1354,f241,f383,f1647])).

fof(f1647,plain,
    ( ! [X5] :
        ( ~ v1_partfun1(k1_xboole_0,X5)
        | ~ v4_relat_1(k1_xboole_0,X5)
        | v4_relat_1(sK3,X5) )
    | ~ spl6_17
    | ~ spl6_63 ),
    inference(superposition,[],[f251,f1105])).

fof(f251,plain,
    ( v4_relat_1(sK3,u1_struct_0(sK0))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl6_17
  <=> v4_relat_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f241,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f109,f107])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1354,plain,
    ( ~ v4_relat_1(sK3,k1_xboole_0)
    | spl6_68 ),
    inference(avatar_component_clause,[],[f1352])).

fof(f1352,plain,
    ( spl6_68
  <=> v4_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f1615,plain,
    ( ~ spl6_6
    | spl6_29
    | ~ spl6_70 ),
    inference(avatar_contradiction_clause,[],[f1613])).

fof(f1613,plain,
    ( $false
    | ~ spl6_6
    | spl6_29
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f167,f1588])).

fof(f1588,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_29
    | ~ spl6_70 ),
    inference(forward_demodulation,[],[f1562,f129])).

fof(f1562,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))
    | spl6_29
    | ~ spl6_70 ),
    inference(superposition,[],[f393,f1363])).

fof(f393,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | spl6_29 ),
    inference(avatar_component_clause,[],[f391])).

fof(f391,plain,
    ( spl6_29
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f167,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl6_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1408,plain,
    ( ~ spl6_7
    | ~ spl6_18
    | ~ spl6_64
    | ~ spl6_69
    | spl6_73 ),
    inference(avatar_contradiction_clause,[],[f1404])).

fof(f1404,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_18
    | ~ spl6_64
    | ~ spl6_69
    | spl6_73 ),
    inference(unit_resulting_resolution,[],[f1359,f256,f1384,f1307])).

fof(f1307,plain,
    ( ! [X0] :
        ( v1_funct_2(sK3,X0,u1_struct_0(sK1))
        | ~ v4_relat_1(sK3,X0)
        | ~ v1_partfun1(sK3,X0) )
    | ~ spl6_7
    | ~ spl6_64 ),
    inference(superposition,[],[f172,f1128])).

fof(f1384,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl6_73 ),
    inference(avatar_component_clause,[],[f1382])).

fof(f1402,plain,
    ( ~ spl6_2
    | spl6_72 ),
    inference(avatar_contradiction_clause,[],[f1399])).

fof(f1399,plain,
    ( $false
    | ~ spl6_2
    | spl6_72 ),
    inference(unit_resulting_resolution,[],[f146,f1380,f239])).

fof(f1380,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl6_72 ),
    inference(avatar_component_clause,[],[f1378])).

fof(f1397,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_71 ),
    inference(avatar_contradiction_clause,[],[f1394])).

fof(f1394,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_71 ),
    inference(unit_resulting_resolution,[],[f141,f146,f1376,f92])).

fof(f1376,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl6_71 ),
    inference(avatar_component_clause,[],[f1374])).

fof(f1393,plain,
    ( ~ spl6_71
    | ~ spl6_72
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_73
    | ~ spl6_74
    | ~ spl6_5
    | ~ spl6_10
    | spl6_13
    | ~ spl6_75
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f531,f191,f1390,f200,f186,f159,f1386,f1382,f154,f149,f1378,f1374])).

fof(f531,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_11 ),
    inference(resolution,[],[f134,f193])).

fof(f1364,plain,
    ( ~ spl6_5
    | ~ spl6_10
    | spl6_69
    | spl6_70
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f510,f191,f1361,f1357,f186,f159])).

fof(f510,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f132,f193])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f1129,plain,
    ( ~ spl6_15
    | ~ spl6_17
    | spl6_64
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f1093,f589,f1127,f249,f223])).

fof(f223,plain,
    ( spl6_15
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f589,plain,
    ( spl6_38
  <=> v1_partfun1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f1093,plain,
    ( ! [X5] :
        ( u1_struct_0(sK0) = X5
        | ~ v4_relat_1(sK3,u1_struct_0(sK0))
        | ~ v1_relat_1(sK3)
        | ~ v1_partfun1(sK3,X5)
        | ~ v4_relat_1(sK3,X5) )
    | ~ spl6_38 ),
    inference(resolution,[],[f389,f591])).

fof(f591,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK0))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f589])).

fof(f389,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X0,X2)
      | X1 = X2
      | ~ v4_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v1_partfun1(X0,X1)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f385])).

fof(f385,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ v1_partfun1(X0,X2)
      | ~ v4_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v1_partfun1(X0,X1)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f103,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f1115,plain,(
    spl6_62 ),
    inference(avatar_contradiction_clause,[],[f1110])).

fof(f1110,plain,
    ( $false
    | spl6_62 ),
    inference(unit_resulting_resolution,[],[f107,f1102,f109])).

fof(f1102,plain,
    ( ~ v4_relat_1(k1_xboole_0,u1_struct_0(sK0))
    | spl6_62 ),
    inference(avatar_component_clause,[],[f1100])).

fof(f1106,plain,
    ( ~ spl6_16
    | ~ spl6_62
    | spl6_63
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f1092,f755,f1104,f1100,f229])).

fof(f229,plain,
    ( spl6_16
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f1092,plain,
    ( ! [X4] :
        ( u1_struct_0(sK0) = X4
        | ~ v4_relat_1(k1_xboole_0,u1_struct_0(sK0))
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_partfun1(k1_xboole_0,X4)
        | ~ v4_relat_1(k1_xboole_0,X4) )
    | ~ spl6_45 ),
    inference(resolution,[],[f389,f757])).

fof(f845,plain,
    ( spl6_49
    | ~ spl6_7
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f668,f559,f170,f842])).

fof(f668,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_7
    | ~ spl6_35 ),
    inference(superposition,[],[f172,f561])).

fof(f816,plain,
    ( spl6_42
    | ~ spl6_12
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f761,f559,f196,f696])).

fof(f761,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_12
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f197,f561])).

fof(f758,plain,
    ( spl6_45
    | ~ spl6_35
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f752,f589,f559,f755])).

fof(f752,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl6_35
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f591,f561])).

fof(f727,plain,
    ( ~ spl6_42
    | spl6_12
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f726,f559,f196,f696])).

fof(f726,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl6_12
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f198,f561])).

fof(f661,plain,
    ( ~ spl6_6
    | spl6_22
    | ~ spl6_39 ),
    inference(avatar_contradiction_clause,[],[f659])).

fof(f659,plain,
    ( $false
    | ~ spl6_6
    | spl6_22
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f167,f638])).

fof(f638,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_22
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f615,f129])).

fof(f615,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))
    | spl6_22
    | ~ spl6_39 ),
    inference(superposition,[],[f292,f595])).

fof(f595,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f593])).

fof(f593,plain,
    ( spl6_39
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f292,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl6_22
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f596,plain,
    ( ~ spl6_5
    | ~ spl6_7
    | spl6_38
    | spl6_39
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f509,f175,f593,f589,f170,f159])).

fof(f509,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | v1_partfun1(sK3,u1_struct_0(sK0))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ spl6_8 ),
    inference(resolution,[],[f132,f177])).

fof(f562,plain,
    ( spl6_35
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f557,f287,f559])).

fof(f287,plain,
    ( spl6_21
  <=> ! [X7] : ~ r2_hidden(X7,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f557,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_21 ),
    inference(resolution,[],[f288,f116])).

fof(f288,plain,
    ( ! [X7] : ~ r2_hidden(X7,sK3)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f287])).

fof(f394,plain,
    ( spl6_21
    | ~ spl6_29
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f275,f191,f391,f287])).

fof(f275,plain,
    ( ! [X8] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ r2_hidden(X8,sK3) )
    | ~ spl6_11 ),
    inference(resolution,[],[f112,f193])).

fof(f384,plain,
    ( spl6_28
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f379,f367,f381])).

fof(f367,plain,
    ( spl6_27
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f379,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_27 ),
    inference(superposition,[],[f105,f369])).

fof(f369,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f367])).

fof(f105,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f370,plain,
    ( spl6_27
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f365,f360,f367])).

fof(f360,plain,
    ( spl6_26
  <=> ! [X4] : ~ r2_hidden(X4,k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f365,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl6_26 ),
    inference(resolution,[],[f361,f116])).

fof(f361,plain,
    ( ! [X4] : ~ r2_hidden(X4,k6_partfun1(k1_xboole_0))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f360])).

fof(f362,plain,
    ( spl6_26
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f272,f208,f165,f360])).

fof(f208,plain,
    ( spl6_14
  <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f272,plain,
    ( ! [X4] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r2_hidden(X4,k6_partfun1(k1_xboole_0)) )
    | ~ spl6_14 ),
    inference(resolution,[],[f112,f210])).

fof(f210,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f208])).

fof(f293,plain,
    ( spl6_21
    | ~ spl6_22
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f274,f175,f290,f287])).

fof(f274,plain,
    ( ! [X7] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ r2_hidden(X7,sK3) )
    | ~ spl6_8 ),
    inference(resolution,[],[f112,f177])).

fof(f257,plain,
    ( spl6_18
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f244,f191,f254])).

fof(f244,plain,
    ( v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl6_11 ),
    inference(resolution,[],[f109,f193])).

fof(f252,plain,
    ( spl6_17
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f243,f175,f249])).

fof(f243,plain,
    ( v4_relat_1(sK3,u1_struct_0(sK0))
    | ~ spl6_8 ),
    inference(resolution,[],[f109,f177])).

fof(f232,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f215,f229])).

fof(f215,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f111,f107])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f227,plain,
    ( spl6_15
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f218,f191,f223])).

fof(f218,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f111,f193])).

fof(f212,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f206,f208])).

fof(f206,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f106,f130])).

fof(f130,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f106,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f204,plain,
    ( spl6_12
    | spl6_13 ),
    inference(avatar_split_clause,[],[f120,f200,f196])).

fof(f120,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,sK0,sK1) ),
    inference(definition_unfolding,[],[f78,f77])).

fof(f77,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f52,f56,f55,f54,f53])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK0,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK0,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | ~ v5_pre_topc(X2,sK0,sK1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | v5_pre_topc(X2,sK0,sK1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | ~ v5_pre_topc(X2,sK0,sK1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | v5_pre_topc(X2,sK0,sK1) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | ~ v5_pre_topc(sK2,sK0,sK1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | v5_pre_topc(sK2,sK0,sK1) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | ~ v5_pre_topc(sK2,sK0,sK1) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | v5_pre_topc(sK2,sK0,sK1) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
      & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,sK0,sK1) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
      & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f78,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f203,plain,
    ( ~ spl6_12
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f119,f200,f196])).

fof(f119,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,sK1) ),
    inference(definition_unfolding,[],[f79,f77])).

fof(f79,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f194,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f76,f191])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f57])).

fof(f189,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f75,f186])).

fof(f75,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

fof(f184,plain,
    ( spl6_9
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f179,f165,f181])).

fof(f179,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_6 ),
    inference(resolution,[],[f102,f167])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f178,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f121,f175])).

fof(f121,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(definition_unfolding,[],[f73,f77])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

fof(f173,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f122,f170])).

fof(f122,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(definition_unfolding,[],[f72,f77])).

fof(f72,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f168,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f108,f165])).

fof(f163,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f123,f159])).

fof(f123,plain,(
    v1_funct_1(sK3) ),
    inference(definition_unfolding,[],[f71,f77])).

fof(f71,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f157,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f70,f154])).

fof(f70,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f152,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f69,f149])).

fof(f69,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f147,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f68,f144])).

fof(f68,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f142,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f67,f139])).

fof(f67,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:46:19 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (8434)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (8435)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (8432)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (8459)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.52  % (8451)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (8442)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (8459)Refutation not found, incomplete strategy% (8459)------------------------------
% 0.22/0.53  % (8459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8448)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (8440)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (8459)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8459)Memory used [KB]: 11001
% 0.22/0.54  % (8459)Time elapsed: 0.121 s
% 0.22/0.54  % (8459)------------------------------
% 0.22/0.54  % (8459)------------------------------
% 0.22/0.54  % (8430)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (8433)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (8452)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (8456)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (8431)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  % (8431)Refutation not found, incomplete strategy% (8431)------------------------------
% 0.22/0.55  % (8431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8431)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8431)Memory used [KB]: 1791
% 0.22/0.55  % (8431)Time elapsed: 0.138 s
% 0.22/0.55  % (8431)------------------------------
% 0.22/0.55  % (8431)------------------------------
% 0.22/0.55  % (8436)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (8455)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (8457)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (8439)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (8458)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (8455)Refutation not found, incomplete strategy% (8455)------------------------------
% 0.22/0.55  % (8455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8455)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8455)Memory used [KB]: 10746
% 0.22/0.55  % (8455)Time elapsed: 0.139 s
% 0.22/0.55  % (8455)------------------------------
% 0.22/0.55  % (8455)------------------------------
% 0.22/0.55  % (8447)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (8442)Refutation not found, incomplete strategy% (8442)------------------------------
% 0.22/0.55  % (8442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8458)Refutation not found, incomplete strategy% (8458)------------------------------
% 0.22/0.55  % (8458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8449)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (8460)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (8443)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (8450)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (8441)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (8447)Refutation not found, incomplete strategy% (8447)------------------------------
% 0.22/0.56  % (8447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (8460)Refutation not found, incomplete strategy% (8460)------------------------------
% 0.22/0.56  % (8460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (8438)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (8460)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (8460)Memory used [KB]: 1791
% 0.22/0.56  % (8460)Time elapsed: 0.154 s
% 0.22/0.56  % (8460)------------------------------
% 0.22/0.56  % (8460)------------------------------
% 0.22/0.56  % (8445)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.57  % (8440)Refutation not found, incomplete strategy% (8440)------------------------------
% 0.22/0.57  % (8440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (8453)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.57  % (8447)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (8447)Memory used [KB]: 10874
% 0.22/0.57  % (8447)Time elapsed: 0.142 s
% 0.22/0.57  % (8447)------------------------------
% 0.22/0.57  % (8447)------------------------------
% 0.22/0.57  % (8458)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (8458)Memory used [KB]: 6396
% 0.22/0.57  % (8458)Time elapsed: 0.141 s
% 0.22/0.57  % (8458)------------------------------
% 0.22/0.57  % (8458)------------------------------
% 0.22/0.58  % (8442)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (8442)Memory used [KB]: 10874
% 0.22/0.58  % (8442)Time elapsed: 0.143 s
% 0.22/0.58  % (8442)------------------------------
% 0.22/0.58  % (8442)------------------------------
% 0.22/0.58  % (8440)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (8440)Memory used [KB]: 11001
% 0.22/0.58  % (8440)Time elapsed: 0.158 s
% 0.22/0.58  % (8440)------------------------------
% 0.22/0.58  % (8440)------------------------------
% 0.22/0.58  % (8444)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.65/0.58  % (8437)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.65/0.58  % (8454)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 2.06/0.68  % (8430)Refutation not found, incomplete strategy% (8430)------------------------------
% 2.06/0.68  % (8430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.68  % (8430)Termination reason: Refutation not found, incomplete strategy
% 2.06/0.68  
% 2.06/0.68  % (8430)Memory used [KB]: 1791
% 2.06/0.68  % (8430)Time elapsed: 0.259 s
% 2.06/0.68  % (8430)------------------------------
% 2.06/0.68  % (8430)------------------------------
% 2.06/0.69  % (8482)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.06/0.69  % (8480)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.06/0.69  % (8482)Refutation not found, incomplete strategy% (8482)------------------------------
% 2.06/0.69  % (8482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.69  % (8482)Termination reason: Refutation not found, incomplete strategy
% 2.06/0.69  
% 2.06/0.69  % (8482)Memory used [KB]: 6268
% 2.06/0.69  % (8482)Time elapsed: 0.112 s
% 2.06/0.69  % (8482)------------------------------
% 2.06/0.69  % (8482)------------------------------
% 2.06/0.70  % (8454)Refutation found. Thanks to Tanya!
% 2.06/0.70  % SZS status Theorem for theBenchmark
% 2.06/0.71  % SZS output start Proof for theBenchmark
% 2.06/0.71  % (8481)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.06/0.71  fof(f4602,plain,(
% 2.06/0.71    $false),
% 2.06/0.71    inference(avatar_sat_refutation,[],[f142,f147,f152,f157,f163,f168,f173,f178,f184,f189,f194,f203,f204,f212,f227,f232,f252,f257,f293,f362,f370,f384,f394,f562,f596,f661,f727,f758,f816,f845,f1106,f1115,f1129,f1364,f1393,f1397,f1402,f1408,f1615,f1731,f1752,f1755,f1758,f1787,f2207,f2211,f2291,f2297,f2567,f2568,f2594,f2601,f2602,f2646,f3493,f3508,f3520,f3528,f3536,f3815,f3914,f3917,f4018,f4032,f4587,f4588,f4589,f4590,f4601])).
% 2.06/0.71  fof(f4601,plain,(
% 2.06/0.71    ~spl6_119 | ~spl6_35 | ~spl6_70 | spl6_85),
% 2.06/0.71    inference(avatar_split_clause,[],[f4600,f1745,f1361,f559,f2560])).
% 2.06/0.71  fof(f2560,plain,(
% 2.06/0.71    spl6_119 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_119])])).
% 2.06/0.71  fof(f559,plain,(
% 2.06/0.71    spl6_35 <=> k1_xboole_0 = sK3),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 2.06/0.71  fof(f1361,plain,(
% 2.06/0.71    spl6_70 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).
% 2.06/0.71  fof(f1745,plain,(
% 2.06/0.71    spl6_85 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).
% 2.06/0.71  fof(f4600,plain,(
% 2.06/0.71    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl6_35 | ~spl6_70 | spl6_85)),
% 2.06/0.71    inference(forward_demodulation,[],[f4599,f561])).
% 2.06/0.71  fof(f561,plain,(
% 2.06/0.71    k1_xboole_0 = sK3 | ~spl6_35),
% 2.06/0.71    inference(avatar_component_clause,[],[f559])).
% 2.06/0.71  fof(f4599,plain,(
% 2.06/0.71    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl6_70 | spl6_85)),
% 2.06/0.71    inference(forward_demodulation,[],[f4598,f129])).
% 2.06/0.71  fof(f129,plain,(
% 2.06/0.71    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.06/0.71    inference(equality_resolution,[],[f88])).
% 2.06/0.71  fof(f88,plain,(
% 2.06/0.71    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.06/0.71    inference(cnf_transformation,[],[f61])).
% 2.06/0.71  fof(f61,plain,(
% 2.06/0.71    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.06/0.71    inference(flattening,[],[f60])).
% 2.06/0.71  fof(f60,plain,(
% 2.06/0.71    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.06/0.71    inference(nnf_transformation,[],[f3])).
% 2.06/0.71  fof(f3,axiom,(
% 2.06/0.71    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.06/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.06/0.71  fof(f4598,plain,(
% 2.06/0.71    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | (~spl6_70 | spl6_85)),
% 2.06/0.71    inference(forward_demodulation,[],[f1747,f1363])).
% 2.06/0.71  fof(f1363,plain,(
% 2.06/0.71    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_70),
% 2.06/0.71    inference(avatar_component_clause,[],[f1361])).
% 2.06/0.71  fof(f1747,plain,(
% 2.06/0.71    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | spl6_85),
% 2.06/0.71    inference(avatar_component_clause,[],[f1745])).
% 2.06/0.71  fof(f4590,plain,(
% 2.06/0.71    k1_xboole_0 != sK3 | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.06/0.71    introduced(theory_tautology_sat_conflict,[])).
% 2.06/0.71  fof(f4589,plain,(
% 2.06/0.71    k1_xboole_0 != sK3 | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)),
% 2.06/0.71    introduced(theory_tautology_sat_conflict,[])).
% 2.06/0.71  fof(f4588,plain,(
% 2.06/0.71    k1_xboole_0 != sK3 | k1_xboole_0 != u1_struct_0(sK0) | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.06/0.71    introduced(theory_tautology_sat_conflict,[])).
% 2.06/0.71  fof(f4587,plain,(
% 2.06/0.71    ~spl6_1 | ~spl6_2 | ~spl6_42 | ~spl6_161 | ~spl6_179 | spl6_118 | ~spl6_129 | ~spl6_165),
% 2.06/0.71    inference(avatar_split_clause,[],[f4582,f3506,f2643,f2556,f4584,f3477,f696,f144,f139])).
% 2.06/0.71  fof(f139,plain,(
% 2.06/0.71    spl6_1 <=> v2_pre_topc(sK0)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.06/0.71  fof(f144,plain,(
% 2.06/0.71    spl6_2 <=> l1_pre_topc(sK0)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.06/0.71  fof(f696,plain,(
% 2.06/0.71    spl6_42 <=> v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 2.06/0.71  fof(f3477,plain,(
% 2.06/0.71    spl6_161 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_161])])).
% 2.06/0.71  fof(f4584,plain,(
% 2.06/0.71    spl6_179 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_179])])).
% 2.06/0.71  fof(f2556,plain,(
% 2.06/0.71    spl6_118 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).
% 2.06/0.71  fof(f2643,plain,(
% 2.06/0.71    spl6_129 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_129])])).
% 2.06/0.71  fof(f3506,plain,(
% 2.06/0.71    spl6_165 <=> ! [X2] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X2),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,X2,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X2),u1_struct_0(sK1)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_165])])).
% 2.06/0.71  fof(f4582,plain,(
% 2.06/0.71    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl6_118 | ~spl6_129 | ~spl6_165)),
% 2.06/0.71    inference(forward_demodulation,[],[f4581,f2645])).
% 2.06/0.71  fof(f2645,plain,(
% 2.06/0.71    k1_xboole_0 = u1_struct_0(sK0) | ~spl6_129),
% 2.06/0.71    inference(avatar_component_clause,[],[f2643])).
% 2.06/0.71  fof(f4581,plain,(
% 2.06/0.71    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl6_118 | ~spl6_129 | ~spl6_165)),
% 2.06/0.71    inference(forward_demodulation,[],[f3800,f2645])).
% 2.06/0.71  fof(f3800,plain,(
% 2.06/0.71    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl6_118 | ~spl6_165)),
% 2.06/0.71    inference(resolution,[],[f2557,f3509])).
% 2.06/0.71  fof(f3509,plain,(
% 2.06/0.71    ( ! [X0] : (v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl6_165),
% 2.06/0.71    inference(resolution,[],[f3507,f107])).
% 2.06/0.71  fof(f107,plain,(
% 2.06/0.71    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.06/0.71    inference(cnf_transformation,[],[f4])).
% 2.06/0.71  fof(f4,axiom,(
% 2.06/0.71    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.06/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.06/0.71  fof(f3507,plain,(
% 2.06/0.71    ( ! [X2] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) | v5_pre_topc(k1_xboole_0,X2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,X2,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X2),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X2),u1_struct_0(sK1)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) ) | ~spl6_165),
% 2.06/0.71    inference(avatar_component_clause,[],[f3506])).
% 2.06/0.71  fof(f2557,plain,(
% 2.06/0.71    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_118),
% 2.06/0.71    inference(avatar_component_clause,[],[f2556])).
% 2.06/0.71  fof(f4032,plain,(
% 2.06/0.71    ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_8 | ~spl6_12 | ~spl6_73 | ~spl6_74 | spl6_75),
% 2.06/0.71    inference(avatar_contradiction_clause,[],[f4020])).
% 2.06/0.71  fof(f4020,plain,(
% 2.06/0.71    $false | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_8 | ~spl6_12 | ~spl6_73 | ~spl6_74 | spl6_75)),
% 2.06/0.71    inference(unit_resulting_resolution,[],[f141,f146,f151,f156,f161,f197,f172,f177,f1392,f1383,f1387,f136])).
% 2.06/0.71  fof(f136,plain,(
% 2.06/0.71    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.06/0.71    inference(duplicate_literal_removal,[],[f125])).
% 2.06/0.71  fof(f125,plain,(
% 2.06/0.71    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.06/0.71    inference(equality_resolution,[],[f80])).
% 2.06/0.71  fof(f80,plain,(
% 2.06/0.71    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.06/0.71    inference(cnf_transformation,[],[f58])).
% 2.06/0.71  fof(f58,plain,(
% 2.06/0.71    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.06/0.71    inference(nnf_transformation,[],[f29])).
% 2.06/0.71  fof(f29,plain,(
% 2.06/0.71    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.06/0.71    inference(flattening,[],[f28])).
% 2.06/0.71  fof(f28,plain,(
% 2.06/0.71    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.06/0.71    inference(ennf_transformation,[],[f22])).
% 2.06/0.71  fof(f22,axiom,(
% 2.06/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 2.06/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).
% 2.06/0.71  fof(f1387,plain,(
% 2.06/0.71    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~spl6_74),
% 2.06/0.71    inference(avatar_component_clause,[],[f1386])).
% 2.06/0.71  fof(f1386,plain,(
% 2.06/0.71    spl6_74 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 2.06/0.71  fof(f1383,plain,(
% 2.06/0.71    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~spl6_73),
% 2.06/0.71    inference(avatar_component_clause,[],[f1382])).
% 2.06/0.71  fof(f1382,plain,(
% 2.06/0.71    spl6_73 <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).
% 2.06/0.71  fof(f1392,plain,(
% 2.06/0.71    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl6_75),
% 2.06/0.71    inference(avatar_component_clause,[],[f1390])).
% 2.06/0.71  fof(f1390,plain,(
% 2.06/0.71    spl6_75 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).
% 2.06/0.71  fof(f177,plain,(
% 2.06/0.71    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl6_8),
% 2.06/0.71    inference(avatar_component_clause,[],[f175])).
% 2.06/0.71  fof(f175,plain,(
% 2.06/0.71    spl6_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.06/0.71  fof(f172,plain,(
% 2.06/0.71    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl6_7),
% 2.06/0.71    inference(avatar_component_clause,[],[f170])).
% 2.06/0.71  fof(f170,plain,(
% 2.06/0.71    spl6_7 <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.06/0.71  fof(f197,plain,(
% 2.06/0.71    v5_pre_topc(sK3,sK0,sK1) | ~spl6_12),
% 2.06/0.71    inference(avatar_component_clause,[],[f196])).
% 2.06/0.71  fof(f196,plain,(
% 2.06/0.71    spl6_12 <=> v5_pre_topc(sK3,sK0,sK1)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 2.06/0.71  fof(f161,plain,(
% 2.06/0.71    v1_funct_1(sK3) | ~spl6_5),
% 2.06/0.71    inference(avatar_component_clause,[],[f159])).
% 2.06/0.71  fof(f159,plain,(
% 2.06/0.71    spl6_5 <=> v1_funct_1(sK3)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.06/0.71  fof(f156,plain,(
% 2.06/0.71    l1_pre_topc(sK1) | ~spl6_4),
% 2.06/0.71    inference(avatar_component_clause,[],[f154])).
% 2.06/0.71  fof(f154,plain,(
% 2.06/0.71    spl6_4 <=> l1_pre_topc(sK1)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.06/0.71  fof(f151,plain,(
% 2.06/0.71    v2_pre_topc(sK1) | ~spl6_3),
% 2.06/0.71    inference(avatar_component_clause,[],[f149])).
% 2.06/0.71  fof(f149,plain,(
% 2.06/0.71    spl6_3 <=> v2_pre_topc(sK1)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.06/0.71  fof(f146,plain,(
% 2.06/0.71    l1_pre_topc(sK0) | ~spl6_2),
% 2.06/0.71    inference(avatar_component_clause,[],[f144])).
% 2.06/0.71  fof(f141,plain,(
% 2.06/0.71    v2_pre_topc(sK0) | ~spl6_1),
% 2.06/0.71    inference(avatar_component_clause,[],[f139])).
% 2.06/0.71  fof(f4018,plain,(
% 2.06/0.71    ~spl6_8 | ~spl6_18 | ~spl6_64 | ~spl6_69 | spl6_74),
% 2.06/0.71    inference(avatar_contradiction_clause,[],[f4004])).
% 2.06/0.71  fof(f4004,plain,(
% 2.06/0.71    $false | (~spl6_8 | ~spl6_18 | ~spl6_64 | ~spl6_69 | spl6_74)),
% 2.06/0.71    inference(unit_resulting_resolution,[],[f1359,f256,f1388,f3833])).
% 2.06/0.71  fof(f3833,plain,(
% 2.06/0.71    ( ! [X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1)))) | ~v4_relat_1(sK3,X1) | ~v1_partfun1(sK3,X1)) ) | (~spl6_8 | ~spl6_64)),
% 2.06/0.71    inference(superposition,[],[f177,f1128])).
% 2.06/0.71  fof(f1128,plain,(
% 2.06/0.71    ( ! [X5] : (u1_struct_0(sK0) = X5 | ~v4_relat_1(sK3,X5) | ~v1_partfun1(sK3,X5)) ) | ~spl6_64),
% 2.06/0.71    inference(avatar_component_clause,[],[f1127])).
% 2.06/0.71  fof(f1127,plain,(
% 2.06/0.71    spl6_64 <=> ! [X5] : (u1_struct_0(sK0) = X5 | ~v4_relat_1(sK3,X5) | ~v1_partfun1(sK3,X5))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 2.06/0.71  fof(f1388,plain,(
% 2.06/0.71    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | spl6_74),
% 2.06/0.71    inference(avatar_component_clause,[],[f1386])).
% 2.06/0.71  fof(f256,plain,(
% 2.06/0.71    v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl6_18),
% 2.06/0.71    inference(avatar_component_clause,[],[f254])).
% 2.06/0.71  fof(f254,plain,(
% 2.06/0.71    spl6_18 <=> v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 2.06/0.71  fof(f1359,plain,(
% 2.06/0.71    v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl6_69),
% 2.06/0.71    inference(avatar_component_clause,[],[f1357])).
% 2.06/0.71  fof(f1357,plain,(
% 2.06/0.71    spl6_69 <=> v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).
% 2.06/0.71  fof(f3917,plain,(
% 2.06/0.71    ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_11 | ~spl6_13 | ~spl6_71 | ~spl6_72 | ~spl6_73 | ~spl6_74 | spl6_75),
% 2.06/0.71    inference(avatar_contradiction_clause,[],[f3915])).
% 2.06/0.71  fof(f3915,plain,(
% 2.06/0.71    $false | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_11 | ~spl6_13 | ~spl6_71 | ~spl6_72 | ~spl6_73 | ~spl6_74 | spl6_75)),
% 2.06/0.71    inference(unit_resulting_resolution,[],[f156,f161,f151,f1375,f1379,f1383,f1387,f201,f188,f193,f1392,f135])).
% 2.06/0.71  fof(f135,plain,(
% 2.06/0.71    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.06/0.71    inference(duplicate_literal_removal,[],[f126])).
% 2.06/0.71  fof(f126,plain,(
% 2.06/0.71    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.06/0.71    inference(equality_resolution,[],[f83])).
% 2.06/0.71  fof(f83,plain,(
% 2.06/0.71    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.06/0.71    inference(cnf_transformation,[],[f59])).
% 2.06/0.71  fof(f59,plain,(
% 2.06/0.71    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.06/0.71    inference(nnf_transformation,[],[f31])).
% 2.06/0.71  fof(f31,plain,(
% 2.06/0.71    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.06/0.71    inference(flattening,[],[f30])).
% 2.06/0.71  fof(f30,plain,(
% 2.06/0.71    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.06/0.71    inference(ennf_transformation,[],[f23])).
% 2.06/0.71  fof(f23,axiom,(
% 2.06/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.06/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).
% 2.06/0.71  fof(f193,plain,(
% 2.06/0.71    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl6_11),
% 2.06/0.71    inference(avatar_component_clause,[],[f191])).
% 2.06/0.71  fof(f191,plain,(
% 2.06/0.71    spl6_11 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 2.06/0.71  fof(f188,plain,(
% 2.06/0.71    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_10),
% 2.06/0.71    inference(avatar_component_clause,[],[f186])).
% 2.06/0.71  fof(f186,plain,(
% 2.06/0.71    spl6_10 <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.06/0.71  fof(f201,plain,(
% 2.06/0.71    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_13),
% 2.06/0.71    inference(avatar_component_clause,[],[f200])).
% 2.06/0.71  fof(f200,plain,(
% 2.06/0.71    spl6_13 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 2.06/0.71  fof(f1379,plain,(
% 2.06/0.71    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl6_72),
% 2.06/0.71    inference(avatar_component_clause,[],[f1378])).
% 2.06/0.71  fof(f1378,plain,(
% 2.06/0.71    spl6_72 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).
% 2.06/0.71  fof(f1375,plain,(
% 2.06/0.71    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl6_71),
% 2.06/0.71    inference(avatar_component_clause,[],[f1374])).
% 2.06/0.71  fof(f1374,plain,(
% 2.06/0.71    spl6_71 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).
% 2.06/0.71  fof(f3914,plain,(
% 2.06/0.71    ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_8 | spl6_12 | ~spl6_73 | ~spl6_74 | ~spl6_75),
% 2.06/0.71    inference(avatar_contradiction_clause,[],[f3902])).
% 2.06/0.71  fof(f3902,plain,(
% 2.06/0.71    $false | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_8 | spl6_12 | ~spl6_73 | ~spl6_74 | ~spl6_75)),
% 2.06/0.71    inference(unit_resulting_resolution,[],[f141,f146,f151,f156,f161,f198,f172,f177,f1391,f1383,f1387,f137])).
% 2.06/0.71  fof(f137,plain,(
% 2.06/0.71    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.06/0.71    inference(duplicate_literal_removal,[],[f124])).
% 2.06/0.71  fof(f124,plain,(
% 2.06/0.71    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.06/0.71    inference(equality_resolution,[],[f81])).
% 2.06/0.71  fof(f81,plain,(
% 2.06/0.71    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.06/0.71    inference(cnf_transformation,[],[f58])).
% 2.06/0.71  fof(f1391,plain,(
% 2.06/0.71    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl6_75),
% 2.06/0.71    inference(avatar_component_clause,[],[f1390])).
% 2.06/0.71  fof(f198,plain,(
% 2.06/0.71    ~v5_pre_topc(sK3,sK0,sK1) | spl6_12),
% 2.06/0.71    inference(avatar_component_clause,[],[f196])).
% 2.06/0.71  fof(f3815,plain,(
% 2.06/0.71    spl6_120),
% 2.06/0.71    inference(avatar_contradiction_clause,[],[f3808])).
% 2.06/0.71  fof(f3808,plain,(
% 2.06/0.71    $false | spl6_120),
% 2.06/0.71    inference(unit_resulting_resolution,[],[f308,f2566])).
% 2.06/0.71  fof(f2566,plain,(
% 2.06/0.71    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | spl6_120),
% 2.06/0.71    inference(avatar_component_clause,[],[f2564])).
% 2.06/0.71  fof(f2564,plain,(
% 2.06/0.71    spl6_120 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).
% 2.06/0.71  fof(f308,plain,(
% 2.06/0.71    ( ! [X4] : (v1_funct_2(k1_xboole_0,X4,k1_xboole_0)) )),
% 2.06/0.71    inference(superposition,[],[f101,f303])).
% 2.06/0.71  fof(f303,plain,(
% 2.06/0.71    ( ! [X0] : (k1_xboole_0 = sK4(X0,k1_xboole_0)) )),
% 2.06/0.71    inference(resolution,[],[f279,f116])).
% 2.06/0.71  fof(f116,plain,(
% 2.06/0.71    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 2.06/0.71    inference(cnf_transformation,[],[f66])).
% 2.06/0.71  fof(f66,plain,(
% 2.06/0.71    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)) | k1_xboole_0 = X0)),
% 2.06/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f50,f65])).
% 2.06/0.71  fof(f65,plain,(
% 2.06/0.71    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)))),
% 2.06/0.71    introduced(choice_axiom,[])).
% 2.06/0.71  fof(f50,plain,(
% 2.06/0.71    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.06/0.71    inference(ennf_transformation,[],[f12])).
% 2.06/0.71  fof(f12,axiom,(
% 2.06/0.71    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.06/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 2.06/0.71  fof(f279,plain,(
% 2.06/0.71    ( ! [X12,X13] : (~r2_hidden(X12,sK4(X13,k1_xboole_0))) )),
% 2.06/0.71    inference(global_subsumption,[],[f108,f277])).
% 2.06/0.71  fof(f277,plain,(
% 2.06/0.71    ( ! [X12,X13] : (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(X12,sK4(X13,k1_xboole_0))) )),
% 2.06/0.71    inference(resolution,[],[f112,f213])).
% 2.06/0.71  fof(f213,plain,(
% 2.06/0.71    ( ! [X0] : (m1_subset_1(sK4(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))) )),
% 2.06/0.71    inference(superposition,[],[f96,f129])).
% 2.06/0.71  fof(f96,plain,(
% 2.06/0.71    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.06/0.71    inference(cnf_transformation,[],[f63])).
% 2.06/0.71  fof(f63,plain,(
% 2.06/0.71    ! [X0,X1] : (v1_funct_2(sK4(X0,X1),X0,X1) & v1_funct_1(sK4(X0,X1)) & v5_relat_1(sK4(X0,X1),X1) & v4_relat_1(sK4(X0,X1),X0) & v1_relat_1(sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f62])).
% 2.06/0.71  fof(f62,plain,(
% 2.06/0.71    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK4(X0,X1),X0,X1) & v1_funct_1(sK4(X0,X1)) & v5_relat_1(sK4(X0,X1),X1) & v4_relat_1(sK4(X0,X1),X0) & v1_relat_1(sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.06/0.71    introduced(choice_axiom,[])).
% 2.06/0.71  fof(f16,axiom,(
% 2.06/0.71    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).
% 2.06/0.71  fof(f112,plain,(
% 2.06/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 2.06/0.71    inference(cnf_transformation,[],[f45])).
% 2.06/0.71  fof(f45,plain,(
% 2.06/0.71    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.06/0.71    inference(ennf_transformation,[],[f6])).
% 2.06/0.71  fof(f6,axiom,(
% 2.06/0.71    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.06/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 2.06/0.71  fof(f108,plain,(
% 2.06/0.71    v1_xboole_0(k1_xboole_0)),
% 2.06/0.71    inference(cnf_transformation,[],[f1])).
% 2.06/0.71  fof(f1,axiom,(
% 2.06/0.71    v1_xboole_0(k1_xboole_0)),
% 2.06/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.06/0.71  fof(f101,plain,(
% 2.06/0.71    ( ! [X0,X1] : (v1_funct_2(sK4(X0,X1),X0,X1)) )),
% 2.06/0.71    inference(cnf_transformation,[],[f63])).
% 2.06/0.71  fof(f3536,plain,(
% 2.06/0.71    k1_xboole_0 != sK3 | k1_xboole_0 != u1_struct_0(sK1) | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)),
% 2.06/0.71    introduced(theory_tautology_sat_conflict,[])).
% 2.06/0.71  fof(f3528,plain,(
% 2.06/0.71    ~spl6_1 | ~spl6_2 | spl6_42 | ~spl6_49 | ~spl6_118 | ~spl6_166),
% 2.06/0.71    inference(avatar_contradiction_clause,[],[f3521])).
% 2.06/0.71  fof(f3521,plain,(
% 2.06/0.71    $false | (~spl6_1 | ~spl6_2 | spl6_42 | ~spl6_49 | ~spl6_118 | ~spl6_166)),
% 2.06/0.71    inference(unit_resulting_resolution,[],[f141,f146,f697,f308,f844,f107,f2558,f3519])).
% 2.06/0.71  fof(f3519,plain,(
% 2.06/0.71    ( ! [X0] : (~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,X0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl6_166),
% 2.06/0.71    inference(avatar_component_clause,[],[f3518])).
% 2.06/0.71  fof(f3518,plain,(
% 2.06/0.71    spl6_166 <=> ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X0,sK1) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_166])])).
% 2.06/0.71  fof(f2558,plain,(
% 2.06/0.71    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_118),
% 2.06/0.71    inference(avatar_component_clause,[],[f2556])).
% 2.06/0.71  fof(f844,plain,(
% 2.06/0.71    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl6_49),
% 2.06/0.71    inference(avatar_component_clause,[],[f842])).
% 2.06/0.71  fof(f842,plain,(
% 2.06/0.71    spl6_49 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 2.06/0.71  fof(f697,plain,(
% 2.06/0.71    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | spl6_42),
% 2.06/0.71    inference(avatar_component_clause,[],[f696])).
% 2.06/0.71  fof(f3520,plain,(
% 2.06/0.71    ~spl6_4 | ~spl6_3 | spl6_166 | ~spl6_70 | ~spl6_124),
% 2.06/0.71    inference(avatar_split_clause,[],[f2614,f2592,f1361,f3518,f149,f154])).
% 2.06/0.71  fof(f2592,plain,(
% 2.06/0.71    spl6_124 <=> ! [X1,X0] : (~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | v5_pre_topc(k1_xboole_0,X0,X1))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_124])])).
% 2.06/0.71  fof(f2614,plain,(
% 2.06/0.71    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,X0,sK1)) ) | (~spl6_70 | ~spl6_124)),
% 2.06/0.71    inference(superposition,[],[f2593,f1363])).
% 2.06/0.71  fof(f2593,plain,(
% 2.06/0.71    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(k1_xboole_0,X0,X1)) ) | ~spl6_124),
% 2.06/0.71    inference(avatar_component_clause,[],[f2592])).
% 2.06/0.71  fof(f3508,plain,(
% 2.06/0.71    ~spl6_4 | ~spl6_3 | spl6_165 | ~spl6_70 | ~spl6_89),
% 2.06/0.71    inference(avatar_split_clause,[],[f2419,f1785,f1361,f3506,f149,f154])).
% 2.06/0.71  fof(f1785,plain,(
% 2.06/0.71    spl6_89 <=> ! [X1,X0] : (~v5_pre_topc(k1_xboole_0,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).
% 2.06/0.71  fof(f2419,plain,(
% 2.06/0.71    ( ! [X2] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X2),k1_xboole_0) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X2),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) | ~v5_pre_topc(k1_xboole_0,X2,sK1) | v5_pre_topc(k1_xboole_0,X2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ) | (~spl6_70 | ~spl6_89)),
% 2.06/0.71    inference(superposition,[],[f1786,f1363])).
% 2.06/0.71  fof(f1786,plain,(
% 2.06/0.71    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k1_xboole_0,X0,X1) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) ) | ~spl6_89),
% 2.06/0.71    inference(avatar_component_clause,[],[f1785])).
% 2.06/0.71  fof(f3493,plain,(
% 2.06/0.71    k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | k1_xboole_0 != sK3 | k1_xboole_0 != u1_struct_0(sK0) | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.06/0.71    introduced(theory_tautology_sat_conflict,[])).
% 2.06/0.71  fof(f2646,plain,(
% 2.06/0.71    ~spl6_62 | spl6_129 | ~spl6_45 | ~spl6_125),
% 2.06/0.71    inference(avatar_split_clause,[],[f2605,f2599,f755,f2643,f1100])).
% 2.06/0.71  fof(f1100,plain,(
% 2.06/0.71    spl6_62 <=> v4_relat_1(k1_xboole_0,u1_struct_0(sK0))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 2.06/0.71  fof(f755,plain,(
% 2.06/0.71    spl6_45 <=> v1_partfun1(k1_xboole_0,u1_struct_0(sK0))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 2.06/0.71  fof(f2599,plain,(
% 2.06/0.71    spl6_125 <=> ! [X1] : (k1_xboole_0 = X1 | ~v1_partfun1(k1_xboole_0,X1) | ~v4_relat_1(k1_xboole_0,X1))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_125])])).
% 2.06/0.71  fof(f2605,plain,(
% 2.06/0.71    k1_xboole_0 = u1_struct_0(sK0) | ~v4_relat_1(k1_xboole_0,u1_struct_0(sK0)) | (~spl6_45 | ~spl6_125)),
% 2.06/0.71    inference(resolution,[],[f2600,f757])).
% 2.06/0.71  fof(f757,plain,(
% 2.06/0.71    v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | ~spl6_45),
% 2.06/0.71    inference(avatar_component_clause,[],[f755])).
% 2.06/0.71  fof(f2600,plain,(
% 2.06/0.71    ( ! [X1] : (~v1_partfun1(k1_xboole_0,X1) | k1_xboole_0 = X1 | ~v4_relat_1(k1_xboole_0,X1)) ) | ~spl6_125),
% 2.06/0.71    inference(avatar_component_clause,[],[f2599])).
% 2.06/0.71  fof(f2602,plain,(
% 2.06/0.71    k1_xboole_0 != sK3 | v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v4_relat_1(sK3,k1_xboole_0)),
% 2.06/0.71    introduced(theory_tautology_sat_conflict,[])).
% 2.06/0.71  fof(f2601,plain,(
% 2.06/0.71    spl6_125 | ~spl6_53 | ~spl6_28 | ~spl6_63),
% 2.06/0.71    inference(avatar_split_clause,[],[f2596,f1104,f381,f866,f2599])).
% 2.06/0.71  fof(f866,plain,(
% 2.06/0.71    spl6_53 <=> v4_relat_1(k1_xboole_0,k1_xboole_0)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 2.06/0.71  fof(f381,plain,(
% 2.06/0.71    spl6_28 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 2.06/0.71  fof(f1104,plain,(
% 2.06/0.71    spl6_63 <=> ! [X4] : (u1_struct_0(sK0) = X4 | ~v4_relat_1(k1_xboole_0,X4) | ~v1_partfun1(k1_xboole_0,X4))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 2.06/0.71  fof(f2596,plain,(
% 2.06/0.71    ( ! [X1] : (~v4_relat_1(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = X1 | ~v4_relat_1(k1_xboole_0,X1) | ~v1_partfun1(k1_xboole_0,X1)) ) | (~spl6_28 | ~spl6_63)),
% 2.06/0.71    inference(resolution,[],[f2076,f383])).
% 2.06/0.71  fof(f383,plain,(
% 2.06/0.71    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl6_28),
% 2.06/0.71    inference(avatar_component_clause,[],[f381])).
% 2.06/0.71  fof(f2076,plain,(
% 2.06/0.71    ( ! [X0,X1] : (~v1_partfun1(k1_xboole_0,X1) | ~v4_relat_1(k1_xboole_0,X1) | X0 = X1 | ~v4_relat_1(k1_xboole_0,X0) | ~v1_partfun1(k1_xboole_0,X0)) ) | ~spl6_63),
% 2.06/0.71    inference(superposition,[],[f1105,f1105])).
% 2.06/0.71  fof(f1105,plain,(
% 2.06/0.71    ( ! [X4] : (u1_struct_0(sK0) = X4 | ~v4_relat_1(k1_xboole_0,X4) | ~v1_partfun1(k1_xboole_0,X4)) ) | ~spl6_63),
% 2.06/0.71    inference(avatar_component_clause,[],[f1104])).
% 2.06/0.71  fof(f2594,plain,(
% 2.06/0.71    ~spl6_9 | spl6_124),
% 2.06/0.71    inference(avatar_split_clause,[],[f535,f2592,f181])).
% 2.06/0.71  fof(f181,plain,(
% 2.06/0.71    spl6_9 <=> v1_funct_1(k1_xboole_0)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 2.06/0.71  fof(f535,plain,(
% 2.06/0.71    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.06/0.71    inference(resolution,[],[f135,f107])).
% 2.06/0.71  fof(f2568,plain,(
% 2.06/0.71    k1_xboole_0 != k6_partfun1(k1_xboole_0) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 2.06/0.71    introduced(theory_tautology_sat_conflict,[])).
% 2.06/0.71  fof(f2567,plain,(
% 2.06/0.71    ~spl6_1 | ~spl6_2 | ~spl6_82 | ~spl6_83 | ~spl6_47 | spl6_118 | ~spl6_9 | ~spl6_98 | ~spl6_119 | ~spl6_120 | ~spl6_11 | ~spl6_35 | ~spl6_70),
% 2.06/0.71    inference(avatar_split_clause,[],[f2541,f1361,f559,f191,f2564,f2560,f2195,f181,f2556,f828,f1737,f1733,f144,f139])).
% 2.06/0.71  fof(f1733,plain,(
% 2.06/0.71    spl6_82 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).
% 2.06/0.71  fof(f1737,plain,(
% 2.06/0.71    spl6_83 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).
% 2.06/0.71  fof(f828,plain,(
% 2.06/0.71    spl6_47 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 2.06/0.71  fof(f2195,plain,(
% 2.06/0.71    spl6_98 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).
% 2.06/0.71  fof(f2541,plain,(
% 2.06/0.71    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_11 | ~spl6_35 | ~spl6_70)),
% 2.06/0.71    inference(forward_demodulation,[],[f2540,f1363])).
% 2.06/0.71  fof(f2540,plain,(
% 2.06/0.71    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_11 | ~spl6_35 | ~spl6_70)),
% 2.06/0.71    inference(forward_demodulation,[],[f2539,f129])).
% 2.06/0.71  fof(f2539,plain,(
% 2.06/0.71    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_11 | ~spl6_35 | ~spl6_70)),
% 2.06/0.71    inference(forward_demodulation,[],[f2538,f1363])).
% 2.06/0.71  fof(f2538,plain,(
% 2.06/0.71    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_11 | ~spl6_35 | ~spl6_70)),
% 2.06/0.71    inference(forward_demodulation,[],[f2394,f1363])).
% 2.06/0.71  fof(f2394,plain,(
% 2.06/0.71    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_11 | ~spl6_35)),
% 2.06/0.71    inference(forward_demodulation,[],[f2393,f561])).
% 2.06/0.71  fof(f2393,plain,(
% 2.06/0.71    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_11 | ~spl6_35)),
% 2.06/0.71    inference(forward_demodulation,[],[f2392,f561])).
% 2.06/0.71  fof(f2392,plain,(
% 2.06/0.71    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_11 | ~spl6_35)),
% 2.06/0.71    inference(forward_demodulation,[],[f2391,f561])).
% 2.06/0.71  fof(f2391,plain,(
% 2.06/0.71    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_11 | ~spl6_35)),
% 2.06/0.71    inference(forward_demodulation,[],[f2390,f561])).
% 2.06/0.71  fof(f2390,plain,(
% 2.06/0.71    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_11 | ~spl6_35)),
% 2.06/0.71    inference(forward_demodulation,[],[f2389,f561])).
% 2.06/0.71  fof(f2389,plain,(
% 2.06/0.71    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_11 | ~spl6_35)),
% 2.06/0.71    inference(forward_demodulation,[],[f549,f561])).
% 2.06/0.71  fof(f549,plain,(
% 2.06/0.71    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl6_11),
% 2.06/0.71    inference(resolution,[],[f137,f193])).
% 2.06/0.71  fof(f2297,plain,(
% 2.06/0.71    spl6_101),
% 2.06/0.71    inference(avatar_contradiction_clause,[],[f2292])).
% 2.06/0.71  fof(f2292,plain,(
% 2.06/0.71    $false | spl6_101),
% 2.06/0.71    inference(unit_resulting_resolution,[],[f107,f2290])).
% 2.06/0.71  fof(f2290,plain,(
% 2.06/0.71    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | spl6_101),
% 2.06/0.71    inference(avatar_component_clause,[],[f2288])).
% 2.06/0.71  fof(f2288,plain,(
% 2.06/0.71    spl6_101 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).
% 2.06/0.71  fof(f2291,plain,(
% 2.06/0.71    ~spl6_101 | ~spl6_35 | spl6_74),
% 2.06/0.71    inference(avatar_split_clause,[],[f2214,f1386,f559,f2288])).
% 2.06/0.71  fof(f2214,plain,(
% 2.06/0.71    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | (~spl6_35 | spl6_74)),
% 2.06/0.71    inference(forward_demodulation,[],[f1388,f561])).
% 2.06/0.71  fof(f2211,plain,(
% 2.06/0.71    k1_xboole_0 != sK3 | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.06/0.71    introduced(theory_tautology_sat_conflict,[])).
% 2.06/0.71  fof(f2207,plain,(
% 2.06/0.71    spl6_98),
% 2.06/0.71    inference(avatar_contradiction_clause,[],[f2199])).
% 2.06/0.71  fof(f2199,plain,(
% 2.06/0.71    $false | spl6_98),
% 2.06/0.71    inference(unit_resulting_resolution,[],[f308,f2197])).
% 2.06/0.71  fof(f2197,plain,(
% 2.06/0.71    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | spl6_98),
% 2.06/0.71    inference(avatar_component_clause,[],[f2195])).
% 2.06/0.71  fof(f1787,plain,(
% 2.06/0.71    ~spl6_9 | spl6_89),
% 2.06/0.71    inference(avatar_split_clause,[],[f529,f1785,f181])).
% 2.06/0.71  fof(f529,plain,(
% 2.06/0.71    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,X1) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.06/0.71    inference(resolution,[],[f134,f107])).
% 2.06/0.71  fof(f134,plain,(
% 2.06/0.71    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.06/0.71    inference(duplicate_literal_removal,[],[f127])).
% 2.06/0.71  fof(f127,plain,(
% 2.06/0.71    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.06/0.71    inference(equality_resolution,[],[f82])).
% 2.06/0.71  fof(f82,plain,(
% 2.06/0.71    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.06/0.71    inference(cnf_transformation,[],[f59])).
% 2.06/0.71  fof(f1758,plain,(
% 2.06/0.71    ~spl6_4 | spl6_83),
% 2.06/0.71    inference(avatar_contradiction_clause,[],[f1756])).
% 2.06/0.71  fof(f1756,plain,(
% 2.06/0.71    $false | (~spl6_4 | spl6_83)),
% 2.06/0.71    inference(unit_resulting_resolution,[],[f156,f1739,f239])).
% 2.06/0.71  fof(f239,plain,(
% 2.06/0.71    ( ! [X0] : (l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 2.06/0.71    inference(resolution,[],[f93,f90])).
% 2.06/0.71  fof(f90,plain,(
% 2.06/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 2.06/0.71    inference(cnf_transformation,[],[f34])).
% 2.06/0.71  fof(f34,plain,(
% 2.06/0.71    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.06/0.71    inference(ennf_transformation,[],[f19])).
% 2.06/0.71  fof(f19,axiom,(
% 2.06/0.71    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 2.06/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 2.06/0.71  fof(f93,plain,(
% 2.06/0.71    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.06/0.71    inference(cnf_transformation,[],[f37])).
% 2.06/0.71  fof(f37,plain,(
% 2.06/0.71    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.06/0.71    inference(ennf_transformation,[],[f20])).
% 2.06/0.71  fof(f20,axiom,(
% 2.06/0.71    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.06/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 2.06/0.71  fof(f1739,plain,(
% 2.06/0.71    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_83),
% 2.06/0.71    inference(avatar_component_clause,[],[f1737])).
% 2.06/0.71  fof(f1755,plain,(
% 2.06/0.71    ~spl6_3 | ~spl6_4 | spl6_82),
% 2.06/0.71    inference(avatar_contradiction_clause,[],[f1753])).
% 2.06/0.71  fof(f1753,plain,(
% 2.06/0.71    $false | (~spl6_3 | ~spl6_4 | spl6_82)),
% 2.06/0.71    inference(unit_resulting_resolution,[],[f151,f156,f1735,f92])).
% 2.06/0.71  fof(f92,plain,(
% 2.06/0.71    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.06/0.71    inference(cnf_transformation,[],[f36])).
% 2.06/0.71  fof(f36,plain,(
% 2.06/0.71    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.06/0.71    inference(flattening,[],[f35])).
% 2.06/0.71  fof(f35,plain,(
% 2.06/0.71    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.06/0.71    inference(ennf_transformation,[],[f21])).
% 2.06/0.71  fof(f21,axiom,(
% 2.06/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.06/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).
% 2.06/0.71  fof(f1735,plain,(
% 2.06/0.71    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_82),
% 2.06/0.71    inference(avatar_component_clause,[],[f1733])).
% 2.06/0.71  fof(f1752,plain,(
% 2.06/0.71    ~spl6_1 | ~spl6_2 | ~spl6_82 | ~spl6_83 | ~spl6_84 | ~spl6_85 | ~spl6_5 | ~spl6_10 | spl6_13 | ~spl6_86 | ~spl6_11),
% 2.06/0.71    inference(avatar_split_clause,[],[f542,f191,f1749,f200,f186,f159,f1745,f1741,f1737,f1733,f144,f139])).
% 2.06/0.71  fof(f1741,plain,(
% 2.06/0.71    spl6_84 <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).
% 2.06/0.71  fof(f1749,plain,(
% 2.06/0.71    spl6_86 <=> v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).
% 2.06/0.71  fof(f542,plain,(
% 2.06/0.71    ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl6_11),
% 2.06/0.71    inference(resolution,[],[f136,f193])).
% 2.06/0.71  fof(f1731,plain,(
% 2.06/0.71    ~spl6_17 | ~spl6_28 | ~spl6_63 | spl6_68),
% 2.06/0.71    inference(avatar_contradiction_clause,[],[f1727])).
% 2.06/0.71  fof(f1727,plain,(
% 2.06/0.71    $false | (~spl6_17 | ~spl6_28 | ~spl6_63 | spl6_68)),
% 2.06/0.71    inference(unit_resulting_resolution,[],[f1354,f241,f383,f1647])).
% 2.06/0.71  fof(f1647,plain,(
% 2.06/0.71    ( ! [X5] : (~v1_partfun1(k1_xboole_0,X5) | ~v4_relat_1(k1_xboole_0,X5) | v4_relat_1(sK3,X5)) ) | (~spl6_17 | ~spl6_63)),
% 2.06/0.71    inference(superposition,[],[f251,f1105])).
% 2.06/0.71  fof(f251,plain,(
% 2.06/0.71    v4_relat_1(sK3,u1_struct_0(sK0)) | ~spl6_17),
% 2.06/0.71    inference(avatar_component_clause,[],[f249])).
% 2.06/0.71  fof(f249,plain,(
% 2.06/0.71    spl6_17 <=> v4_relat_1(sK3,u1_struct_0(sK0))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 2.06/0.71  fof(f241,plain,(
% 2.06/0.71    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 2.06/0.71    inference(resolution,[],[f109,f107])).
% 2.06/0.71  fof(f109,plain,(
% 2.06/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.06/0.71    inference(cnf_transformation,[],[f43])).
% 2.06/0.71  fof(f43,plain,(
% 2.06/0.71    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.71    inference(ennf_transformation,[],[f9])).
% 2.06/0.71  fof(f9,axiom,(
% 2.06/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.06/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.06/0.71  fof(f1354,plain,(
% 2.06/0.71    ~v4_relat_1(sK3,k1_xboole_0) | spl6_68),
% 2.06/0.71    inference(avatar_component_clause,[],[f1352])).
% 2.06/0.71  fof(f1352,plain,(
% 2.06/0.71    spl6_68 <=> v4_relat_1(sK3,k1_xboole_0)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 2.06/0.71  fof(f1615,plain,(
% 2.06/0.71    ~spl6_6 | spl6_29 | ~spl6_70),
% 2.06/0.71    inference(avatar_contradiction_clause,[],[f1613])).
% 2.06/0.71  fof(f1613,plain,(
% 2.06/0.71    $false | (~spl6_6 | spl6_29 | ~spl6_70)),
% 2.06/0.71    inference(subsumption_resolution,[],[f167,f1588])).
% 2.06/0.71  fof(f1588,plain,(
% 2.06/0.71    ~v1_xboole_0(k1_xboole_0) | (spl6_29 | ~spl6_70)),
% 2.06/0.71    inference(forward_demodulation,[],[f1562,f129])).
% 2.06/0.71  fof(f1562,plain,(
% 2.06/0.71    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)) | (spl6_29 | ~spl6_70)),
% 2.06/0.71    inference(superposition,[],[f393,f1363])).
% 2.06/0.71  fof(f393,plain,(
% 2.06/0.71    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | spl6_29),
% 2.06/0.71    inference(avatar_component_clause,[],[f391])).
% 2.06/0.71  fof(f391,plain,(
% 2.06/0.71    spl6_29 <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 2.06/0.71  fof(f167,plain,(
% 2.06/0.71    v1_xboole_0(k1_xboole_0) | ~spl6_6),
% 2.06/0.71    inference(avatar_component_clause,[],[f165])).
% 2.06/0.71  fof(f165,plain,(
% 2.06/0.71    spl6_6 <=> v1_xboole_0(k1_xboole_0)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.06/0.71  fof(f1408,plain,(
% 2.06/0.71    ~spl6_7 | ~spl6_18 | ~spl6_64 | ~spl6_69 | spl6_73),
% 2.06/0.71    inference(avatar_contradiction_clause,[],[f1404])).
% 2.06/0.71  fof(f1404,plain,(
% 2.06/0.71    $false | (~spl6_7 | ~spl6_18 | ~spl6_64 | ~spl6_69 | spl6_73)),
% 2.06/0.71    inference(unit_resulting_resolution,[],[f1359,f256,f1384,f1307])).
% 2.06/0.71  fof(f1307,plain,(
% 2.06/0.71    ( ! [X0] : (v1_funct_2(sK3,X0,u1_struct_0(sK1)) | ~v4_relat_1(sK3,X0) | ~v1_partfun1(sK3,X0)) ) | (~spl6_7 | ~spl6_64)),
% 2.06/0.71    inference(superposition,[],[f172,f1128])).
% 2.06/0.71  fof(f1384,plain,(
% 2.06/0.71    ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | spl6_73),
% 2.06/0.71    inference(avatar_component_clause,[],[f1382])).
% 2.06/0.71  fof(f1402,plain,(
% 2.06/0.71    ~spl6_2 | spl6_72),
% 2.06/0.71    inference(avatar_contradiction_clause,[],[f1399])).
% 2.06/0.71  fof(f1399,plain,(
% 2.06/0.71    $false | (~spl6_2 | spl6_72)),
% 2.06/0.71    inference(unit_resulting_resolution,[],[f146,f1380,f239])).
% 2.06/0.71  fof(f1380,plain,(
% 2.06/0.71    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl6_72),
% 2.06/0.71    inference(avatar_component_clause,[],[f1378])).
% 2.06/0.71  fof(f1397,plain,(
% 2.06/0.71    ~spl6_1 | ~spl6_2 | spl6_71),
% 2.06/0.71    inference(avatar_contradiction_clause,[],[f1394])).
% 2.06/0.71  fof(f1394,plain,(
% 2.06/0.71    $false | (~spl6_1 | ~spl6_2 | spl6_71)),
% 2.06/0.71    inference(unit_resulting_resolution,[],[f141,f146,f1376,f92])).
% 2.06/0.71  fof(f1376,plain,(
% 2.06/0.71    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl6_71),
% 2.06/0.71    inference(avatar_component_clause,[],[f1374])).
% 2.06/0.71  fof(f1393,plain,(
% 2.06/0.71    ~spl6_71 | ~spl6_72 | ~spl6_3 | ~spl6_4 | ~spl6_73 | ~spl6_74 | ~spl6_5 | ~spl6_10 | spl6_13 | ~spl6_75 | ~spl6_11),
% 2.06/0.71    inference(avatar_split_clause,[],[f531,f191,f1390,f200,f186,f159,f1386,f1382,f154,f149,f1378,f1374])).
% 2.06/0.71  fof(f531,plain,(
% 2.06/0.71    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl6_11),
% 2.06/0.71    inference(resolution,[],[f134,f193])).
% 2.06/0.71  fof(f1364,plain,(
% 2.06/0.71    ~spl6_5 | ~spl6_10 | spl6_69 | spl6_70 | ~spl6_11),
% 2.06/0.71    inference(avatar_split_clause,[],[f510,f191,f1361,f1357,f186,f159])).
% 2.06/0.71  fof(f510,plain,(
% 2.06/0.71    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK3) | ~spl6_11),
% 2.06/0.71    inference(resolution,[],[f132,f193])).
% 2.06/0.71  fof(f132,plain,(
% 2.06/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.06/0.71    inference(duplicate_literal_removal,[],[f84])).
% 2.06/0.71  fof(f84,plain,(
% 2.06/0.71    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.06/0.71    inference(cnf_transformation,[],[f33])).
% 2.06/0.71  fof(f33,plain,(
% 2.06/0.71    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.06/0.71    inference(flattening,[],[f32])).
% 2.06/0.71  fof(f32,plain,(
% 2.06/0.71    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.06/0.71    inference(ennf_transformation,[],[f18])).
% 2.06/0.71  fof(f18,axiom,(
% 2.06/0.71    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.06/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 2.06/0.71  fof(f1129,plain,(
% 2.06/0.71    ~spl6_15 | ~spl6_17 | spl6_64 | ~spl6_38),
% 2.06/0.71    inference(avatar_split_clause,[],[f1093,f589,f1127,f249,f223])).
% 2.06/0.71  fof(f223,plain,(
% 2.06/0.71    spl6_15 <=> v1_relat_1(sK3)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 2.06/0.71  fof(f589,plain,(
% 2.06/0.71    spl6_38 <=> v1_partfun1(sK3,u1_struct_0(sK0))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 2.06/0.71  fof(f1093,plain,(
% 2.06/0.71    ( ! [X5] : (u1_struct_0(sK0) = X5 | ~v4_relat_1(sK3,u1_struct_0(sK0)) | ~v1_relat_1(sK3) | ~v1_partfun1(sK3,X5) | ~v4_relat_1(sK3,X5)) ) | ~spl6_38),
% 2.06/0.71    inference(resolution,[],[f389,f591])).
% 2.06/0.71  fof(f591,plain,(
% 2.06/0.71    v1_partfun1(sK3,u1_struct_0(sK0)) | ~spl6_38),
% 2.06/0.71    inference(avatar_component_clause,[],[f589])).
% 2.06/0.71  fof(f389,plain,(
% 2.06/0.71    ( ! [X2,X0,X1] : (~v1_partfun1(X0,X2) | X1 = X2 | ~v4_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X1)) )),
% 2.06/0.71    inference(duplicate_literal_removal,[],[f385])).
% 2.06/0.71  fof(f385,plain,(
% 2.06/0.71    ( ! [X2,X0,X1] : (X1 = X2 | ~v1_partfun1(X0,X2) | ~v4_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 2.06/0.71    inference(superposition,[],[f103,f103])).
% 2.06/0.71  fof(f103,plain,(
% 2.06/0.71    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.06/0.71    inference(cnf_transformation,[],[f64])).
% 2.06/0.71  fof(f64,plain,(
% 2.06/0.71    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.06/0.71    inference(nnf_transformation,[],[f42])).
% 2.06/0.71  fof(f42,plain,(
% 2.06/0.71    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.06/0.71    inference(flattening,[],[f41])).
% 2.06/0.71  fof(f41,plain,(
% 2.06/0.71    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.06/0.71    inference(ennf_transformation,[],[f14])).
% 2.06/0.71  fof(f14,axiom,(
% 2.06/0.71    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.06/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 2.06/0.71  fof(f1115,plain,(
% 2.06/0.71    spl6_62),
% 2.06/0.71    inference(avatar_contradiction_clause,[],[f1110])).
% 2.06/0.71  fof(f1110,plain,(
% 2.06/0.71    $false | spl6_62),
% 2.06/0.71    inference(unit_resulting_resolution,[],[f107,f1102,f109])).
% 2.06/0.71  fof(f1102,plain,(
% 2.06/0.71    ~v4_relat_1(k1_xboole_0,u1_struct_0(sK0)) | spl6_62),
% 2.06/0.71    inference(avatar_component_clause,[],[f1100])).
% 2.06/0.71  fof(f1106,plain,(
% 2.06/0.71    ~spl6_16 | ~spl6_62 | spl6_63 | ~spl6_45),
% 2.06/0.71    inference(avatar_split_clause,[],[f1092,f755,f1104,f1100,f229])).
% 2.06/0.71  fof(f229,plain,(
% 2.06/0.71    spl6_16 <=> v1_relat_1(k1_xboole_0)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 2.06/0.71  fof(f1092,plain,(
% 2.06/0.71    ( ! [X4] : (u1_struct_0(sK0) = X4 | ~v4_relat_1(k1_xboole_0,u1_struct_0(sK0)) | ~v1_relat_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,X4) | ~v4_relat_1(k1_xboole_0,X4)) ) | ~spl6_45),
% 2.06/0.71    inference(resolution,[],[f389,f757])).
% 2.06/0.71  fof(f845,plain,(
% 2.06/0.71    spl6_49 | ~spl6_7 | ~spl6_35),
% 2.06/0.71    inference(avatar_split_clause,[],[f668,f559,f170,f842])).
% 2.06/0.71  fof(f668,plain,(
% 2.06/0.71    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_7 | ~spl6_35)),
% 2.06/0.71    inference(superposition,[],[f172,f561])).
% 2.06/0.71  fof(f816,plain,(
% 2.06/0.71    spl6_42 | ~spl6_12 | ~spl6_35),
% 2.06/0.71    inference(avatar_split_clause,[],[f761,f559,f196,f696])).
% 2.06/0.71  fof(f761,plain,(
% 2.06/0.71    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_12 | ~spl6_35)),
% 2.06/0.71    inference(forward_demodulation,[],[f197,f561])).
% 2.06/0.71  fof(f758,plain,(
% 2.06/0.71    spl6_45 | ~spl6_35 | ~spl6_38),
% 2.06/0.71    inference(avatar_split_clause,[],[f752,f589,f559,f755])).
% 2.06/0.71  fof(f752,plain,(
% 2.06/0.71    v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | (~spl6_35 | ~spl6_38)),
% 2.06/0.71    inference(forward_demodulation,[],[f591,f561])).
% 2.06/0.71  fof(f727,plain,(
% 2.06/0.71    ~spl6_42 | spl6_12 | ~spl6_35),
% 2.06/0.71    inference(avatar_split_clause,[],[f726,f559,f196,f696])).
% 2.06/0.71  fof(f726,plain,(
% 2.06/0.71    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl6_12 | ~spl6_35)),
% 2.06/0.71    inference(forward_demodulation,[],[f198,f561])).
% 2.06/0.71  fof(f661,plain,(
% 2.06/0.71    ~spl6_6 | spl6_22 | ~spl6_39),
% 2.06/0.71    inference(avatar_contradiction_clause,[],[f659])).
% 2.06/0.71  fof(f659,plain,(
% 2.06/0.71    $false | (~spl6_6 | spl6_22 | ~spl6_39)),
% 2.06/0.71    inference(subsumption_resolution,[],[f167,f638])).
% 2.06/0.71  fof(f638,plain,(
% 2.06/0.71    ~v1_xboole_0(k1_xboole_0) | (spl6_22 | ~spl6_39)),
% 2.06/0.71    inference(forward_demodulation,[],[f615,f129])).
% 2.06/0.71  fof(f615,plain,(
% 2.06/0.71    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) | (spl6_22 | ~spl6_39)),
% 2.06/0.71    inference(superposition,[],[f292,f595])).
% 2.06/0.71  fof(f595,plain,(
% 2.06/0.71    k1_xboole_0 = u1_struct_0(sK1) | ~spl6_39),
% 2.06/0.71    inference(avatar_component_clause,[],[f593])).
% 2.06/0.71  fof(f593,plain,(
% 2.06/0.71    spl6_39 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 2.06/0.71  fof(f292,plain,(
% 2.06/0.71    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | spl6_22),
% 2.06/0.71    inference(avatar_component_clause,[],[f290])).
% 2.06/0.71  fof(f290,plain,(
% 2.06/0.71    spl6_22 <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 2.06/0.71  fof(f596,plain,(
% 2.06/0.71    ~spl6_5 | ~spl6_7 | spl6_38 | spl6_39 | ~spl6_8),
% 2.06/0.71    inference(avatar_split_clause,[],[f509,f175,f593,f589,f170,f159])).
% 2.06/0.71  fof(f509,plain,(
% 2.06/0.71    k1_xboole_0 = u1_struct_0(sK1) | v1_partfun1(sK3,u1_struct_0(sK0)) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~spl6_8),
% 2.06/0.71    inference(resolution,[],[f132,f177])).
% 2.06/0.71  fof(f562,plain,(
% 2.06/0.71    spl6_35 | ~spl6_21),
% 2.06/0.71    inference(avatar_split_clause,[],[f557,f287,f559])).
% 2.06/0.71  fof(f287,plain,(
% 2.06/0.71    spl6_21 <=> ! [X7] : ~r2_hidden(X7,sK3)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 2.06/0.71  fof(f557,plain,(
% 2.06/0.71    k1_xboole_0 = sK3 | ~spl6_21),
% 2.06/0.71    inference(resolution,[],[f288,f116])).
% 2.06/0.71  fof(f288,plain,(
% 2.06/0.71    ( ! [X7] : (~r2_hidden(X7,sK3)) ) | ~spl6_21),
% 2.06/0.71    inference(avatar_component_clause,[],[f287])).
% 2.06/0.71  fof(f394,plain,(
% 2.06/0.71    spl6_21 | ~spl6_29 | ~spl6_11),
% 2.06/0.71    inference(avatar_split_clause,[],[f275,f191,f391,f287])).
% 2.06/0.71  fof(f275,plain,(
% 2.06/0.71    ( ! [X8] : (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~r2_hidden(X8,sK3)) ) | ~spl6_11),
% 2.06/0.71    inference(resolution,[],[f112,f193])).
% 2.06/0.71  fof(f384,plain,(
% 2.06/0.71    spl6_28 | ~spl6_27),
% 2.06/0.71    inference(avatar_split_clause,[],[f379,f367,f381])).
% 2.06/0.71  fof(f367,plain,(
% 2.06/0.71    spl6_27 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 2.06/0.71  fof(f379,plain,(
% 2.06/0.71    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl6_27),
% 2.06/0.71    inference(superposition,[],[f105,f369])).
% 2.06/0.71  fof(f369,plain,(
% 2.06/0.71    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl6_27),
% 2.06/0.71    inference(avatar_component_clause,[],[f367])).
% 2.06/0.71  fof(f105,plain,(
% 2.06/0.71    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 2.06/0.71    inference(cnf_transformation,[],[f15])).
% 2.06/0.71  fof(f15,axiom,(
% 2.06/0.71    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.06/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.06/0.71  fof(f370,plain,(
% 2.06/0.71    spl6_27 | ~spl6_26),
% 2.06/0.71    inference(avatar_split_clause,[],[f365,f360,f367])).
% 2.06/0.71  fof(f360,plain,(
% 2.06/0.71    spl6_26 <=> ! [X4] : ~r2_hidden(X4,k6_partfun1(k1_xboole_0))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 2.06/0.71  fof(f365,plain,(
% 2.06/0.71    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl6_26),
% 2.06/0.71    inference(resolution,[],[f361,f116])).
% 2.06/0.71  fof(f361,plain,(
% 2.06/0.71    ( ! [X4] : (~r2_hidden(X4,k6_partfun1(k1_xboole_0))) ) | ~spl6_26),
% 2.06/0.71    inference(avatar_component_clause,[],[f360])).
% 2.06/0.71  fof(f362,plain,(
% 2.06/0.71    spl6_26 | ~spl6_6 | ~spl6_14),
% 2.06/0.71    inference(avatar_split_clause,[],[f272,f208,f165,f360])).
% 2.06/0.71  fof(f208,plain,(
% 2.06/0.71    spl6_14 <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 2.06/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 2.06/0.71  fof(f272,plain,(
% 2.06/0.71    ( ! [X4] : (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(X4,k6_partfun1(k1_xboole_0))) ) | ~spl6_14),
% 2.06/0.71    inference(resolution,[],[f112,f210])).
% 2.06/0.71  fof(f210,plain,(
% 2.06/0.71    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl6_14),
% 2.06/0.71    inference(avatar_component_clause,[],[f208])).
% 2.06/0.71  fof(f293,plain,(
% 2.06/0.71    spl6_21 | ~spl6_22 | ~spl6_8),
% 2.06/0.71    inference(avatar_split_clause,[],[f274,f175,f290,f287])).
% 2.06/0.71  fof(f274,plain,(
% 2.06/0.71    ( ! [X7] : (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~r2_hidden(X7,sK3)) ) | ~spl6_8),
% 2.06/0.71    inference(resolution,[],[f112,f177])).
% 2.06/0.71  fof(f257,plain,(
% 2.06/0.71    spl6_18 | ~spl6_11),
% 2.06/0.71    inference(avatar_split_clause,[],[f244,f191,f254])).
% 2.06/0.71  fof(f244,plain,(
% 2.06/0.71    v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl6_11),
% 2.06/0.71    inference(resolution,[],[f109,f193])).
% 2.06/0.71  fof(f252,plain,(
% 2.06/0.71    spl6_17 | ~spl6_8),
% 2.06/0.71    inference(avatar_split_clause,[],[f243,f175,f249])).
% 2.06/0.71  fof(f243,plain,(
% 2.06/0.71    v4_relat_1(sK3,u1_struct_0(sK0)) | ~spl6_8),
% 2.06/0.71    inference(resolution,[],[f109,f177])).
% 2.06/0.71  fof(f232,plain,(
% 2.06/0.71    spl6_16),
% 2.06/0.71    inference(avatar_split_clause,[],[f215,f229])).
% 2.06/0.71  fof(f215,plain,(
% 2.06/0.71    v1_relat_1(k1_xboole_0)),
% 2.06/0.71    inference(resolution,[],[f111,f107])).
% 2.06/0.71  fof(f111,plain,(
% 2.06/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.06/0.71    inference(cnf_transformation,[],[f44])).
% 2.06/0.71  fof(f44,plain,(
% 2.06/0.71    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.71    inference(ennf_transformation,[],[f8])).
% 2.06/0.71  fof(f8,axiom,(
% 2.06/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.06/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.06/0.71  fof(f227,plain,(
% 2.06/0.71    spl6_15 | ~spl6_11),
% 2.06/0.71    inference(avatar_split_clause,[],[f218,f191,f223])).
% 2.06/0.71  fof(f218,plain,(
% 2.06/0.71    v1_relat_1(sK3) | ~spl6_11),
% 2.06/0.71    inference(resolution,[],[f111,f193])).
% 2.06/0.71  fof(f212,plain,(
% 2.06/0.71    spl6_14),
% 2.06/0.71    inference(avatar_split_clause,[],[f206,f208])).
% 2.06/0.71  fof(f206,plain,(
% 2.06/0.71    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 2.06/0.71    inference(superposition,[],[f106,f130])).
% 2.06/0.71  fof(f130,plain,(
% 2.06/0.71    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.06/0.71    inference(equality_resolution,[],[f87])).
% 2.06/0.71  fof(f87,plain,(
% 2.06/0.71    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.06/0.71    inference(cnf_transformation,[],[f61])).
% 2.06/0.71  fof(f106,plain,(
% 2.06/0.71    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.06/0.71    inference(cnf_transformation,[],[f15])).
% 2.06/0.71  fof(f204,plain,(
% 2.06/0.71    spl6_12 | spl6_13),
% 2.06/0.71    inference(avatar_split_clause,[],[f120,f200,f196])).
% 2.06/0.71  fof(f120,plain,(
% 2.06/0.71    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK3,sK0,sK1)),
% 2.06/0.71    inference(definition_unfolding,[],[f78,f77])).
% 2.06/0.71  fof(f77,plain,(
% 2.06/0.71    sK2 = sK3),
% 2.06/0.71    inference(cnf_transformation,[],[f57])).
% 2.06/0.71  fof(f57,plain,(
% 2.06/0.71    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.06/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f52,f56,f55,f54,f53])).
% 2.06/0.71  fof(f53,plain,(
% 2.06/0.71    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.06/0.71    introduced(choice_axiom,[])).
% 2.06/0.71  fof(f54,plain,(
% 2.06/0.71    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 2.06/0.71    introduced(choice_axiom,[])).
% 2.06/0.71  fof(f55,plain,(
% 2.06/0.71    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 2.06/0.71    introduced(choice_axiom,[])).
% 2.06/0.71  fof(f56,plain,(
% 2.06/0.71    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3))),
% 2.06/0.71    introduced(choice_axiom,[])).
% 2.06/0.71  fof(f52,plain,(
% 2.06/0.71    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.06/0.71    inference(flattening,[],[f51])).
% 2.06/0.71  fof(f51,plain,(
% 2.06/0.71    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.06/0.71    inference(nnf_transformation,[],[f27])).
% 2.06/0.71  fof(f27,plain,(
% 2.06/0.71    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.06/0.71    inference(flattening,[],[f26])).
% 2.06/0.71  fof(f26,plain,(
% 2.06/0.71    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.06/0.71    inference(ennf_transformation,[],[f25])).
% 2.06/0.71  fof(f25,negated_conjecture,(
% 2.06/0.71    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.06/0.71    inference(negated_conjecture,[],[f24])).
% 2.06/0.71  fof(f24,conjecture,(
% 2.06/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.06/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).
% 2.06/0.71  fof(f78,plain,(
% 2.06/0.71    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 2.06/0.71    inference(cnf_transformation,[],[f57])).
% 2.06/0.71  fof(f203,plain,(
% 2.06/0.71    ~spl6_12 | ~spl6_13),
% 2.06/0.71    inference(avatar_split_clause,[],[f119,f200,f196])).
% 2.06/0.71  fof(f119,plain,(
% 2.06/0.71    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,sK1)),
% 2.06/0.71    inference(definition_unfolding,[],[f79,f77])).
% 2.06/0.71  fof(f79,plain,(
% 2.06/0.71    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 2.06/0.71    inference(cnf_transformation,[],[f57])).
% 2.06/0.71  fof(f194,plain,(
% 2.06/0.71    spl6_11),
% 2.06/0.71    inference(avatar_split_clause,[],[f76,f191])).
% 2.06/0.71  fof(f76,plain,(
% 2.06/0.71    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.06/0.71    inference(cnf_transformation,[],[f57])).
% 2.06/0.71  fof(f189,plain,(
% 2.06/0.71    spl6_10),
% 2.06/0.71    inference(avatar_split_clause,[],[f75,f186])).
% 2.06/0.71  fof(f75,plain,(
% 2.06/0.71    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.06/0.71    inference(cnf_transformation,[],[f57])).
% 2.06/0.71  fof(f184,plain,(
% 2.06/0.71    spl6_9 | ~spl6_6),
% 2.06/0.71    inference(avatar_split_clause,[],[f179,f165,f181])).
% 2.06/0.71  fof(f179,plain,(
% 2.06/0.71    v1_funct_1(k1_xboole_0) | ~spl6_6),
% 2.06/0.71    inference(resolution,[],[f102,f167])).
% 2.06/0.71  fof(f102,plain,(
% 2.06/0.71    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 2.06/0.71    inference(cnf_transformation,[],[f40])).
% 2.06/0.71  fof(f40,plain,(
% 2.06/0.71    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 2.06/0.71    inference(ennf_transformation,[],[f7])).
% 2.06/0.71  fof(f7,axiom,(
% 2.06/0.71    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 2.06/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 2.06/0.71  fof(f178,plain,(
% 2.06/0.71    spl6_8),
% 2.06/0.71    inference(avatar_split_clause,[],[f121,f175])).
% 2.06/0.71  fof(f121,plain,(
% 2.06/0.71    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.06/0.71    inference(definition_unfolding,[],[f73,f77])).
% 2.06/0.71  fof(f73,plain,(
% 2.06/0.71    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.06/0.71    inference(cnf_transformation,[],[f57])).
% 2.06/0.71  fof(f173,plain,(
% 2.06/0.71    spl6_7),
% 2.06/0.71    inference(avatar_split_clause,[],[f122,f170])).
% 2.06/0.71  fof(f122,plain,(
% 2.06/0.71    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.06/0.71    inference(definition_unfolding,[],[f72,f77])).
% 2.06/0.71  fof(f72,plain,(
% 2.06/0.71    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.06/0.71    inference(cnf_transformation,[],[f57])).
% 2.06/0.71  fof(f168,plain,(
% 2.06/0.71    spl6_6),
% 2.06/0.71    inference(avatar_split_clause,[],[f108,f165])).
% 2.06/0.71  fof(f163,plain,(
% 2.06/0.71    spl6_5),
% 2.06/0.71    inference(avatar_split_clause,[],[f123,f159])).
% 2.06/0.71  fof(f123,plain,(
% 2.06/0.71    v1_funct_1(sK3)),
% 2.06/0.71    inference(definition_unfolding,[],[f71,f77])).
% 2.06/0.71  fof(f71,plain,(
% 2.06/0.71    v1_funct_1(sK2)),
% 2.06/0.71    inference(cnf_transformation,[],[f57])).
% 2.06/0.71  fof(f157,plain,(
% 2.06/0.71    spl6_4),
% 2.06/0.71    inference(avatar_split_clause,[],[f70,f154])).
% 2.06/0.71  fof(f70,plain,(
% 2.06/0.71    l1_pre_topc(sK1)),
% 2.06/0.71    inference(cnf_transformation,[],[f57])).
% 2.06/0.71  fof(f152,plain,(
% 2.06/0.71    spl6_3),
% 2.06/0.71    inference(avatar_split_clause,[],[f69,f149])).
% 2.06/0.71  fof(f69,plain,(
% 2.06/0.71    v2_pre_topc(sK1)),
% 2.06/0.71    inference(cnf_transformation,[],[f57])).
% 2.06/0.71  fof(f147,plain,(
% 2.06/0.71    spl6_2),
% 2.06/0.71    inference(avatar_split_clause,[],[f68,f144])).
% 2.06/0.71  fof(f68,plain,(
% 2.06/0.71    l1_pre_topc(sK0)),
% 2.06/0.71    inference(cnf_transformation,[],[f57])).
% 2.06/0.71  fof(f142,plain,(
% 2.06/0.71    spl6_1),
% 2.06/0.71    inference(avatar_split_clause,[],[f67,f139])).
% 2.06/0.71  fof(f67,plain,(
% 2.06/0.71    v2_pre_topc(sK0)),
% 2.06/0.71    inference(cnf_transformation,[],[f57])).
% 2.06/0.71  % SZS output end Proof for theBenchmark
% 2.06/0.71  % (8454)------------------------------
% 2.06/0.71  % (8454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.71  % (8454)Termination reason: Refutation
% 2.06/0.71  
% 2.06/0.71  % (8454)Memory used [KB]: 13560
% 2.06/0.71  % (8454)Time elapsed: 0.295 s
% 2.06/0.71  % (8454)------------------------------
% 2.06/0.71  % (8454)------------------------------
% 2.06/0.71  % (8428)Success in time 0.343 s
%------------------------------------------------------------------------------
