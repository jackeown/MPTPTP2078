%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:46 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 297 expanded)
%              Number of leaves         :   40 ( 125 expanded)
%              Depth                    :    8
%              Number of atoms          :  671 (1504 expanded)
%              Number of equality atoms :   52 ( 148 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f531,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f61,f69,f73,f77,f81,f85,f89,f93,f101,f114,f122,f141,f153,f157,f174,f178,f183,f192,f196,f220,f231,f241,f254,f258,f269,f273,f428,f446,f458,f473,f474,f493,f522])).

fof(f522,plain,
    ( spl6_9
    | ~ spl6_41
    | ~ spl6_58
    | ~ spl6_63 ),
    inference(avatar_contradiction_clause,[],[f521])).

fof(f521,plain,
    ( $false
    | spl6_9
    | ~ spl6_41
    | ~ spl6_58
    | ~ spl6_63 ),
    inference(subsumption_resolution,[],[f505,f84])).

fof(f84,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl6_9
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f505,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl6_41
    | ~ spl6_58
    | ~ spl6_63 ),
    inference(backward_demodulation,[],[f445,f501])).

fof(f501,plain,
    ( ! [X4] : k2_xboole_0(u1_struct_0(sK1),X4) = X4
    | ~ spl6_41
    | ~ spl6_63 ),
    inference(resolution,[],[f492,f268])).

fof(f268,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(X0,X1,X1),X0)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl6_41
  <=> ! [X1,X0] :
        ( r2_hidden(sK5(X0,X1,X1),X0)
        | k2_xboole_0(X0,X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f492,plain,
    ( ! [X0] : ~ r2_hidden(X0,u1_struct_0(sK1))
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f491])).

fof(f491,plain,
    ( spl6_63
  <=> ! [X0] : ~ r2_hidden(X0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f445,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f444])).

fof(f444,plain,
    ( spl6_58
  <=> m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f493,plain,
    ( spl6_63
    | ~ spl6_18
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f475,f471,f120,f491])).

fof(f120,plain,
    ( spl6_18
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X0)
        | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f471,plain,
    ( spl6_61
  <=> ! [X2] : ~ r2_hidden(X2,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f475,plain,
    ( ! [X0] : ~ r2_hidden(X0,u1_struct_0(sK1))
    | ~ spl6_18
    | ~ spl6_61 ),
    inference(resolution,[],[f472,f121])).

fof(f121,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(X3,k2_xboole_0(X0,X1))
        | ~ r2_hidden(X3,X0) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f120])).

fof(f472,plain,
    ( ! [X2] : ~ r2_hidden(X2,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f471])).

fof(f474,plain,
    ( spl6_60
    | spl6_59
    | ~ spl6_16
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f447,f444,f112,f449,f464])).

fof(f464,plain,
    ( spl6_60
  <=> v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f449,plain,
    ( spl6_59
  <=> r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f112,plain,
    ( spl6_16
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f447,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl6_16
    | ~ spl6_58 ),
    inference(resolution,[],[f445,f113])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | r2_hidden(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f112])).

fof(f473,plain,
    ( spl6_61
    | ~ spl6_11
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f469,f464,f91,f471])).

fof(f91,plain,
    ( spl6_11
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f469,plain,
    ( ! [X2] : ~ r2_hidden(X2,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl6_11
    | ~ spl6_60 ),
    inference(resolution,[],[f465,f92])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f91])).

fof(f465,plain,
    ( v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f464])).

fof(f458,plain,
    ( spl6_8
    | ~ spl6_40
    | spl6_42
    | ~ spl6_59 ),
    inference(avatar_contradiction_clause,[],[f453])).

fof(f453,plain,
    ( $false
    | spl6_8
    | ~ spl6_40
    | spl6_42
    | ~ spl6_59 ),
    inference(unit_resulting_resolution,[],[f272,f80,f450,f257])).

fof(f257,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X0,X2)
        | ~ r2_hidden(X0,k2_xboole_0(X2,X1))
        | r2_hidden(X0,X1) )
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl6_40
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k2_xboole_0(X2,X1))
        | m1_subset_1(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f450,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f449])).

fof(f80,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl6_8
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f272,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | spl6_42 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl6_42
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f446,plain,
    ( spl6_58
    | spl6_1
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f438,f426,f87,f71,f51,f444])).

fof(f51,plain,
    ( spl6_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f71,plain,
    ( spl6_6
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f87,plain,
    ( spl6_10
  <=> m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f426,plain,
    ( spl6_56
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,sK1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f438,plain,
    ( m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | spl6_1
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_56 ),
    inference(backward_demodulation,[],[f88,f436])).

fof(f436,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl6_1
    | ~ spl6_6
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f433,f52])).

fof(f52,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f433,plain,
    ( v2_struct_0(sK2)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl6_6
    | ~ spl6_56 ),
    inference(resolution,[],[f427,f72])).

fof(f72,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f427,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,sK1,X1)) )
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f426])).

fof(f88,plain,
    ( m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f87])).

fof(f428,plain,
    ( spl6_56
    | spl6_2
    | ~ spl6_7
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f248,f239,f75,f55,f426])).

fof(f55,plain,
    ( spl6_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f75,plain,
    ( spl6_7
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f239,plain,
    ( spl6_38
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f248,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,sK1,X1)) )
    | spl6_2
    | ~ spl6_7
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f245,f56])).

fof(f56,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f245,plain,
    ( ! [X1] :
        ( v2_struct_0(sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,sK1,X1)) )
    | ~ spl6_7
    | ~ spl6_38 ),
    inference(resolution,[],[f240,f76])).

fof(f76,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f240,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f239])).

fof(f273,plain,
    ( ~ spl6_42
    | ~ spl6_18
    | spl6_39 ),
    inference(avatar_split_clause,[],[f262,f252,f120,f271])).

fof(f252,plain,
    ( spl6_39
  <=> r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f262,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl6_18
    | spl6_39 ),
    inference(resolution,[],[f253,f121])).

fof(f253,plain,
    ( ~ r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)))
    | spl6_39 ),
    inference(avatar_component_clause,[],[f252])).

fof(f269,plain,
    ( spl6_41
    | ~ spl6_25
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f204,f194,f155,f267])).

fof(f155,plain,
    ( spl6_25
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK5(X0,X1,X2),X1)
        | ~ r2_hidden(sK5(X0,X1,X2),X2)
        | k2_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f194,plain,
    ( spl6_32
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK5(X0,X1,X2),X0)
        | r2_hidden(sK5(X0,X1,X2),X1)
        | r2_hidden(sK5(X0,X1,X2),X2)
        | k2_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f204,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(X0,X1,X1),X0)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl6_25
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f200,f156])).

fof(f156,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK5(X0,X1,X2),X2)
        | ~ r2_hidden(sK5(X0,X1,X2),X1)
        | k2_xboole_0(X0,X1) = X2 )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f155])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(X0,X1,X1),X1)
        | r2_hidden(sK5(X0,X1,X1),X0)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl6_32 ),
    inference(factoring,[],[f195])).

fof(f195,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK5(X0,X1,X2),X2)
        | r2_hidden(sK5(X0,X1,X2),X1)
        | r2_hidden(sK5(X0,X1,X2),X0)
        | k2_xboole_0(X0,X1) = X2 )
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f194])).

fof(f258,plain,
    ( spl6_40
    | ~ spl6_13
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f142,f139,f99,f256])).

fof(f99,plain,
    ( spl6_13
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f139,plain,
    ( spl6_22
  <=> ! [X1,X3,X0] :
        ( r2_hidden(X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f142,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k2_xboole_0(X2,X1))
        | m1_subset_1(X0,X2) )
    | ~ spl6_13
    | ~ spl6_22 ),
    inference(resolution,[],[f140,f100])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | m1_subset_1(X1,X0) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f99])).

fof(f140,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f139])).

fof(f254,plain,
    ( ~ spl6_39
    | spl6_9
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f207,f190,f83,f252])).

fof(f190,plain,
    ( spl6_31
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(X1,X1))
        | m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f207,plain,
    ( ~ r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)))
    | spl6_9
    | ~ spl6_31 ),
    inference(resolution,[],[f191,f84])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,X1)
        | ~ r2_hidden(X0,k2_xboole_0(X1,X1)) )
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f190])).

fof(f241,plain,
    ( spl6_38
    | spl6_3
    | ~ spl6_5
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f237,f229,f67,f59,f239])).

fof(f59,plain,
    ( spl6_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f67,plain,
    ( spl6_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f229,plain,
    ( spl6_36
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f237,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | spl6_3
    | ~ spl6_5
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f236,f60])).

fof(f60,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f236,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | ~ spl6_5
    | ~ spl6_36 ),
    inference(resolution,[],[f230,f68])).

fof(f68,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f230,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) )
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f229])).

fof(f231,plain,
    ( spl6_36
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f223,f218,f181,f176,f172,f229])).

fof(f172,plain,
    ( spl6_27
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f176,plain,
    ( spl6_28
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v1_pre_topc(k1_tsep_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f181,plain,
    ( spl6_29
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f218,plain,
    ( spl6_35
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(k1_tsep_1(X0,X1,X2))
        | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
        | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f223,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) )
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f222,f182])).

fof(f182,plain,
    ( ! [X2,X0,X1] :
        ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0) )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f181])).

fof(f222,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) )
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f221,f177])).

fof(f177,plain,
    ( ! [X2,X0,X1] :
        ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f176])).

fof(f221,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
        | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) )
    | ~ spl6_27
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f219,f173])).

fof(f173,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f172])).

fof(f219,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(k1_tsep_1(X0,X1,X2))
        | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
        | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) )
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f218])).

fof(f220,plain,(
    spl6_35 ),
    inference(avatar_split_clause,[],[f45,f218])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ v1_pre_topc(X3)
      | ~ m1_pre_topc(X3,X0)
      | u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f196,plain,(
    spl6_32 ),
    inference(avatar_split_clause,[],[f39,f194])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f192,plain,
    ( spl6_31
    | ~ spl6_13
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f161,f151,f99,f190])).

fof(f151,plain,
    ( spl6_24
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k2_xboole_0(X1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_xboole_0(X1,X1))
        | m1_subset_1(X0,X1) )
    | ~ spl6_13
    | ~ spl6_24 ),
    inference(resolution,[],[f152,f100])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k2_xboole_0(X1,X1)) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f151])).

fof(f183,plain,(
    spl6_29 ),
    inference(avatar_split_clause,[],[f36,f181])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f178,plain,(
    spl6_28 ),
    inference(avatar_split_clause,[],[f35,f176])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v1_pre_topc(k1_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f174,plain,(
    spl6_27 ),
    inference(avatar_split_clause,[],[f34,f172])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f157,plain,(
    spl6_25 ),
    inference(avatar_split_clause,[],[f38,f155])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f153,plain,
    ( spl6_24
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f143,f139,f151])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k2_xboole_0(X1,X1)) )
    | ~ spl6_22 ),
    inference(factoring,[],[f140])).

fof(f141,plain,(
    spl6_22 ),
    inference(avatar_split_clause,[],[f48,f139])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f122,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f47,f120])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f114,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f33,f112])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f101,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f49,f99])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f32,f29])).

% (10304)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f93,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f29,f91])).

fof(f89,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f18,f87])).

fof(f18,plain,(
    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
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
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => X3 != X5 ) ) ) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,negated_conjecture,(
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
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X1))
                           => X3 != X4 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ~ ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X2))
                         => X3 != X4 )
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => X3 != X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tmap_1)).

fof(f85,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f44,f83])).

fof(f44,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X4 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f81,plain,(
    ~ spl6_8 ),
    inference(avatar_split_clause,[],[f43,f79])).

fof(f43,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK1))
      | sK3 != X5 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f77,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f22,f75])).

fof(f22,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f73,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f20,f71])).

fof(f20,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f69,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f25,f67])).

fof(f25,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f61,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f23,f59])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f21,f55])).

fof(f21,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f53,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f19,f51])).

fof(f19,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:43:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.43  % (10297)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (10301)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (10290)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (10295)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (10293)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (10287)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (10299)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (10296)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.53  % (10291)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.53  % (10300)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.53  % (10288)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (10292)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (10305)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.53  % (10288)Refutation not found, incomplete strategy% (10288)------------------------------
% 0.22/0.53  % (10288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10288)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (10288)Memory used [KB]: 10618
% 0.22/0.53  % (10288)Time elapsed: 0.097 s
% 0.22/0.53  % (10288)------------------------------
% 0.22/0.53  % (10288)------------------------------
% 0.22/0.54  % (10289)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.54  % (10294)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.47/0.54  % (10296)Refutation found. Thanks to Tanya!
% 1.47/0.54  % SZS status Theorem for theBenchmark
% 1.47/0.54  % SZS output start Proof for theBenchmark
% 1.47/0.54  fof(f531,plain,(
% 1.47/0.54    $false),
% 1.47/0.54    inference(avatar_sat_refutation,[],[f53,f57,f61,f69,f73,f77,f81,f85,f89,f93,f101,f114,f122,f141,f153,f157,f174,f178,f183,f192,f196,f220,f231,f241,f254,f258,f269,f273,f428,f446,f458,f473,f474,f493,f522])).
% 1.47/0.54  fof(f522,plain,(
% 1.47/0.54    spl6_9 | ~spl6_41 | ~spl6_58 | ~spl6_63),
% 1.47/0.54    inference(avatar_contradiction_clause,[],[f521])).
% 1.47/0.54  fof(f521,plain,(
% 1.47/0.54    $false | (spl6_9 | ~spl6_41 | ~spl6_58 | ~spl6_63)),
% 1.47/0.54    inference(subsumption_resolution,[],[f505,f84])).
% 1.47/0.54  fof(f84,plain,(
% 1.47/0.54    ~m1_subset_1(sK3,u1_struct_0(sK2)) | spl6_9),
% 1.47/0.54    inference(avatar_component_clause,[],[f83])).
% 1.47/0.54  fof(f83,plain,(
% 1.47/0.54    spl6_9 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.47/0.54  fof(f505,plain,(
% 1.47/0.54    m1_subset_1(sK3,u1_struct_0(sK2)) | (~spl6_41 | ~spl6_58 | ~spl6_63)),
% 1.47/0.54    inference(backward_demodulation,[],[f445,f501])).
% 1.47/0.54  fof(f501,plain,(
% 1.47/0.54    ( ! [X4] : (k2_xboole_0(u1_struct_0(sK1),X4) = X4) ) | (~spl6_41 | ~spl6_63)),
% 1.47/0.54    inference(resolution,[],[f492,f268])).
% 1.47/0.54  fof(f268,plain,(
% 1.47/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) ) | ~spl6_41),
% 1.47/0.54    inference(avatar_component_clause,[],[f267])).
% 1.47/0.54  fof(f267,plain,(
% 1.47/0.54    spl6_41 <=> ! [X1,X0] : (r2_hidden(sK5(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1)),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 1.47/0.54  fof(f492,plain,(
% 1.47/0.54    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1))) ) | ~spl6_63),
% 1.47/0.54    inference(avatar_component_clause,[],[f491])).
% 1.47/0.54  fof(f491,plain,(
% 1.47/0.54    spl6_63 <=> ! [X0] : ~r2_hidden(X0,u1_struct_0(sK1))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 1.47/0.54  fof(f445,plain,(
% 1.47/0.54    m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl6_58),
% 1.47/0.54    inference(avatar_component_clause,[],[f444])).
% 1.47/0.54  fof(f444,plain,(
% 1.47/0.54    spl6_58 <=> m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 1.47/0.54  fof(f493,plain,(
% 1.47/0.54    spl6_63 | ~spl6_18 | ~spl6_61),
% 1.47/0.54    inference(avatar_split_clause,[],[f475,f471,f120,f491])).
% 1.47/0.54  fof(f120,plain,(
% 1.47/0.54    spl6_18 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1)))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.47/0.54  fof(f471,plain,(
% 1.47/0.54    spl6_61 <=> ! [X2] : ~r2_hidden(X2,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 1.47/0.54  fof(f475,plain,(
% 1.47/0.54    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1))) ) | (~spl6_18 | ~spl6_61)),
% 1.47/0.54    inference(resolution,[],[f472,f121])).
% 1.47/0.54  fof(f121,plain,(
% 1.47/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X0)) ) | ~spl6_18),
% 1.47/0.54    inference(avatar_component_clause,[],[f120])).
% 1.47/0.54  fof(f472,plain,(
% 1.47/0.54    ( ! [X2] : (~r2_hidden(X2,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))) ) | ~spl6_61),
% 1.47/0.54    inference(avatar_component_clause,[],[f471])).
% 1.47/0.54  fof(f474,plain,(
% 1.47/0.54    spl6_60 | spl6_59 | ~spl6_16 | ~spl6_58),
% 1.47/0.54    inference(avatar_split_clause,[],[f447,f444,f112,f449,f464])).
% 1.47/0.54  fof(f464,plain,(
% 1.47/0.54    spl6_60 <=> v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 1.47/0.54  fof(f449,plain,(
% 1.47/0.54    spl6_59 <=> r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 1.47/0.54  fof(f112,plain,(
% 1.47/0.54    spl6_16 <=> ! [X1,X0] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.47/0.54  fof(f447,plain,(
% 1.47/0.54    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | (~spl6_16 | ~spl6_58)),
% 1.47/0.54    inference(resolution,[],[f445,f113])).
% 1.47/0.54  fof(f113,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) ) | ~spl6_16),
% 1.47/0.54    inference(avatar_component_clause,[],[f112])).
% 1.47/0.54  fof(f473,plain,(
% 1.47/0.54    spl6_61 | ~spl6_11 | ~spl6_60),
% 1.47/0.54    inference(avatar_split_clause,[],[f469,f464,f91,f471])).
% 1.47/0.54  fof(f91,plain,(
% 1.47/0.54    spl6_11 <=> ! [X1,X0] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.47/0.54  fof(f469,plain,(
% 1.47/0.54    ( ! [X2] : (~r2_hidden(X2,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))) ) | (~spl6_11 | ~spl6_60)),
% 1.47/0.54    inference(resolution,[],[f465,f92])).
% 1.47/0.54  fof(f92,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) ) | ~spl6_11),
% 1.47/0.54    inference(avatar_component_clause,[],[f91])).
% 1.47/0.54  fof(f465,plain,(
% 1.47/0.54    v1_xboole_0(k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl6_60),
% 1.47/0.54    inference(avatar_component_clause,[],[f464])).
% 1.47/0.54  fof(f458,plain,(
% 1.47/0.54    spl6_8 | ~spl6_40 | spl6_42 | ~spl6_59),
% 1.47/0.54    inference(avatar_contradiction_clause,[],[f453])).
% 1.47/0.54  fof(f453,plain,(
% 1.47/0.54    $false | (spl6_8 | ~spl6_40 | spl6_42 | ~spl6_59)),
% 1.47/0.54    inference(unit_resulting_resolution,[],[f272,f80,f450,f257])).
% 1.47/0.54  fof(f257,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~r2_hidden(X0,k2_xboole_0(X2,X1)) | r2_hidden(X0,X1)) ) | ~spl6_40),
% 1.47/0.54    inference(avatar_component_clause,[],[f256])).
% 1.47/0.54  fof(f256,plain,(
% 1.47/0.54    spl6_40 <=> ! [X1,X0,X2] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X2,X1)) | m1_subset_1(X0,X2))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 1.47/0.54  fof(f450,plain,(
% 1.47/0.54    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl6_59),
% 1.47/0.54    inference(avatar_component_clause,[],[f449])).
% 1.47/0.54  fof(f80,plain,(
% 1.47/0.54    ~m1_subset_1(sK3,u1_struct_0(sK1)) | spl6_8),
% 1.47/0.54    inference(avatar_component_clause,[],[f79])).
% 1.47/0.54  fof(f79,plain,(
% 1.47/0.54    spl6_8 <=> m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.47/0.54  fof(f272,plain,(
% 1.47/0.54    ~r2_hidden(sK3,u1_struct_0(sK2)) | spl6_42),
% 1.47/0.54    inference(avatar_component_clause,[],[f271])).
% 1.47/0.54  fof(f271,plain,(
% 1.47/0.54    spl6_42 <=> r2_hidden(sK3,u1_struct_0(sK2))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 1.47/0.54  fof(f446,plain,(
% 1.47/0.54    spl6_58 | spl6_1 | ~spl6_6 | ~spl6_10 | ~spl6_56),
% 1.47/0.54    inference(avatar_split_clause,[],[f438,f426,f87,f71,f51,f444])).
% 1.47/0.54  fof(f51,plain,(
% 1.47/0.54    spl6_1 <=> v2_struct_0(sK2)),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.47/0.54  fof(f71,plain,(
% 1.47/0.54    spl6_6 <=> m1_pre_topc(sK2,sK0)),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.47/0.54  fof(f87,plain,(
% 1.47/0.54    spl6_10 <=> m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.47/0.54  fof(f426,plain,(
% 1.47/0.54    spl6_56 <=> ! [X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,sK1,X1)))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).
% 1.47/0.54  fof(f438,plain,(
% 1.47/0.54    m1_subset_1(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | (spl6_1 | ~spl6_6 | ~spl6_10 | ~spl6_56)),
% 1.47/0.54    inference(backward_demodulation,[],[f88,f436])).
% 1.47/0.54  fof(f436,plain,(
% 1.47/0.54    u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (spl6_1 | ~spl6_6 | ~spl6_56)),
% 1.47/0.54    inference(subsumption_resolution,[],[f433,f52])).
% 1.47/0.54  fof(f52,plain,(
% 1.47/0.54    ~v2_struct_0(sK2) | spl6_1),
% 1.47/0.54    inference(avatar_component_clause,[],[f51])).
% 1.47/0.54  fof(f433,plain,(
% 1.47/0.54    v2_struct_0(sK2) | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (~spl6_6 | ~spl6_56)),
% 1.47/0.54    inference(resolution,[],[f427,f72])).
% 1.47/0.54  fof(f72,plain,(
% 1.47/0.54    m1_pre_topc(sK2,sK0) | ~spl6_6),
% 1.47/0.54    inference(avatar_component_clause,[],[f71])).
% 1.47/0.54  fof(f427,plain,(
% 1.47/0.54    ( ! [X1] : (~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,sK1,X1))) ) | ~spl6_56),
% 1.47/0.54    inference(avatar_component_clause,[],[f426])).
% 1.47/0.54  fof(f88,plain,(
% 1.47/0.54    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~spl6_10),
% 1.47/0.54    inference(avatar_component_clause,[],[f87])).
% 1.47/0.54  fof(f428,plain,(
% 1.47/0.54    spl6_56 | spl6_2 | ~spl6_7 | ~spl6_38),
% 1.47/0.54    inference(avatar_split_clause,[],[f248,f239,f75,f55,f426])).
% 1.47/0.54  fof(f55,plain,(
% 1.47/0.54    spl6_2 <=> v2_struct_0(sK1)),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.47/0.54  fof(f75,plain,(
% 1.47/0.54    spl6_7 <=> m1_pre_topc(sK1,sK0)),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.47/0.54  fof(f239,plain,(
% 1.47/0.54    spl6_38 <=> ! [X1,X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 1.47/0.54  fof(f248,plain,(
% 1.47/0.54    ( ! [X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,sK1,X1))) ) | (spl6_2 | ~spl6_7 | ~spl6_38)),
% 1.47/0.54    inference(subsumption_resolution,[],[f245,f56])).
% 1.47/0.54  fof(f56,plain,(
% 1.47/0.54    ~v2_struct_0(sK1) | spl6_2),
% 1.47/0.54    inference(avatar_component_clause,[],[f55])).
% 1.47/0.54  fof(f245,plain,(
% 1.47/0.54    ( ! [X1] : (v2_struct_0(sK1) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,sK1,X1))) ) | (~spl6_7 | ~spl6_38)),
% 1.47/0.54    inference(resolution,[],[f240,f76])).
% 1.47/0.54  fof(f76,plain,(
% 1.47/0.54    m1_pre_topc(sK1,sK0) | ~spl6_7),
% 1.47/0.54    inference(avatar_component_clause,[],[f75])).
% 1.47/0.54  fof(f240,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1))) ) | ~spl6_38),
% 1.47/0.54    inference(avatar_component_clause,[],[f239])).
% 1.47/0.54  fof(f273,plain,(
% 1.47/0.54    ~spl6_42 | ~spl6_18 | spl6_39),
% 1.47/0.54    inference(avatar_split_clause,[],[f262,f252,f120,f271])).
% 1.47/0.54  fof(f252,plain,(
% 1.47/0.54    spl6_39 <=> r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 1.47/0.54  fof(f262,plain,(
% 1.47/0.54    ~r2_hidden(sK3,u1_struct_0(sK2)) | (~spl6_18 | spl6_39)),
% 1.47/0.54    inference(resolution,[],[f253,f121])).
% 1.47/0.54  fof(f253,plain,(
% 1.47/0.54    ~r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))) | spl6_39),
% 1.47/0.54    inference(avatar_component_clause,[],[f252])).
% 1.47/0.54  fof(f269,plain,(
% 1.47/0.54    spl6_41 | ~spl6_25 | ~spl6_32),
% 1.47/0.54    inference(avatar_split_clause,[],[f204,f194,f155,f267])).
% 1.47/0.54  fof(f155,plain,(
% 1.47/0.54    spl6_25 <=> ! [X1,X0,X2] : (~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2)),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.47/0.54  fof(f194,plain,(
% 1.47/0.54    spl6_32 <=> ! [X1,X0,X2] : (r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2)),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 1.47/0.54  fof(f204,plain,(
% 1.47/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) ) | (~spl6_25 | ~spl6_32)),
% 1.47/0.54    inference(subsumption_resolution,[],[f200,f156])).
% 1.47/0.54  fof(f156,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1) | k2_xboole_0(X0,X1) = X2) ) | ~spl6_25),
% 1.47/0.54    inference(avatar_component_clause,[],[f155])).
% 1.47/0.54  fof(f200,plain,(
% 1.47/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,X1),X1) | r2_hidden(sK5(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) ) | ~spl6_32),
% 1.47/0.54    inference(factoring,[],[f195])).
% 1.47/0.54  fof(f195,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) ) | ~spl6_32),
% 1.47/0.54    inference(avatar_component_clause,[],[f194])).
% 1.47/0.54  fof(f258,plain,(
% 1.47/0.54    spl6_40 | ~spl6_13 | ~spl6_22),
% 1.47/0.54    inference(avatar_split_clause,[],[f142,f139,f99,f256])).
% 1.47/0.54  fof(f99,plain,(
% 1.47/0.54    spl6_13 <=> ! [X1,X0] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.47/0.54  fof(f139,plain,(
% 1.47/0.54    spl6_22 <=> ! [X1,X3,X0] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,k2_xboole_0(X0,X1)))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.47/0.54  fof(f142,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X2,X1)) | m1_subset_1(X0,X2)) ) | (~spl6_13 | ~spl6_22)),
% 1.47/0.54    inference(resolution,[],[f140,f100])).
% 1.47/0.54  fof(f100,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) ) | ~spl6_13),
% 1.47/0.54    inference(avatar_component_clause,[],[f99])).
% 1.47/0.54  fof(f140,plain,(
% 1.47/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,k2_xboole_0(X0,X1))) ) | ~spl6_22),
% 1.47/0.54    inference(avatar_component_clause,[],[f139])).
% 1.47/0.54  fof(f254,plain,(
% 1.47/0.54    ~spl6_39 | spl6_9 | ~spl6_31),
% 1.47/0.54    inference(avatar_split_clause,[],[f207,f190,f83,f252])).
% 1.47/0.54  fof(f190,plain,(
% 1.47/0.54    spl6_31 <=> ! [X1,X0] : (~r2_hidden(X0,k2_xboole_0(X1,X1)) | m1_subset_1(X0,X1))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 1.47/0.54  fof(f207,plain,(
% 1.47/0.54    ~r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))) | (spl6_9 | ~spl6_31)),
% 1.47/0.54    inference(resolution,[],[f191,f84])).
% 1.47/0.54  fof(f191,plain,(
% 1.47/0.54    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,X1))) ) | ~spl6_31),
% 1.47/0.54    inference(avatar_component_clause,[],[f190])).
% 1.47/0.54  fof(f241,plain,(
% 1.47/0.54    spl6_38 | spl6_3 | ~spl6_5 | ~spl6_36),
% 1.47/0.54    inference(avatar_split_clause,[],[f237,f229,f67,f59,f239])).
% 1.47/0.54  fof(f59,plain,(
% 1.47/0.54    spl6_3 <=> v2_struct_0(sK0)),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.47/0.54  fof(f67,plain,(
% 1.47/0.54    spl6_5 <=> l1_pre_topc(sK0)),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.47/0.54  fof(f229,plain,(
% 1.47/0.54    spl6_36 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 1.47/0.54  fof(f237,plain,(
% 1.47/0.54    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1))) ) | (spl6_3 | ~spl6_5 | ~spl6_36)),
% 1.47/0.54    inference(subsumption_resolution,[],[f236,f60])).
% 1.47/0.54  fof(f60,plain,(
% 1.47/0.54    ~v2_struct_0(sK0) | spl6_3),
% 1.47/0.54    inference(avatar_component_clause,[],[f59])).
% 1.47/0.54  fof(f236,plain,(
% 1.47/0.54    ( ! [X0,X1] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1))) ) | (~spl6_5 | ~spl6_36)),
% 1.47/0.54    inference(resolution,[],[f230,f68])).
% 1.47/0.54  fof(f68,plain,(
% 1.47/0.54    l1_pre_topc(sK0) | ~spl6_5),
% 1.47/0.54    inference(avatar_component_clause,[],[f67])).
% 1.47/0.54  fof(f230,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))) ) | ~spl6_36),
% 1.47/0.54    inference(avatar_component_clause,[],[f229])).
% 1.47/0.54  fof(f231,plain,(
% 1.47/0.54    spl6_36 | ~spl6_27 | ~spl6_28 | ~spl6_29 | ~spl6_35),
% 1.47/0.54    inference(avatar_split_clause,[],[f223,f218,f181,f176,f172,f229])).
% 1.47/0.54  fof(f172,plain,(
% 1.47/0.54    spl6_27 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~v2_struct_0(k1_tsep_1(X0,X1,X2)))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.47/0.54  fof(f176,plain,(
% 1.47/0.54    spl6_28 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v1_pre_topc(k1_tsep_1(X0,X1,X2)))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 1.47/0.54  fof(f181,plain,(
% 1.47/0.54    spl6_29 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 1.47/0.54  fof(f218,plain,(
% 1.47/0.54    spl6_35 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 1.47/0.54  fof(f223,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))) ) | (~spl6_27 | ~spl6_28 | ~spl6_29 | ~spl6_35)),
% 1.47/0.54    inference(subsumption_resolution,[],[f222,f182])).
% 1.47/0.54  fof(f182,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) ) | ~spl6_29),
% 1.47/0.54    inference(avatar_component_clause,[],[f181])).
% 1.47/0.54  fof(f222,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))) ) | (~spl6_27 | ~spl6_28 | ~spl6_35)),
% 1.47/0.54    inference(subsumption_resolution,[],[f221,f177])).
% 1.47/0.54  fof(f177,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) ) | ~spl6_28),
% 1.47/0.54    inference(avatar_component_clause,[],[f176])).
% 1.47/0.54  fof(f221,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))) ) | (~spl6_27 | ~spl6_35)),
% 1.47/0.54    inference(subsumption_resolution,[],[f219,f173])).
% 1.47/0.54  fof(f173,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) ) | ~spl6_27),
% 1.47/0.54    inference(avatar_component_clause,[],[f172])).
% 1.47/0.54  fof(f219,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))) ) | ~spl6_35),
% 1.47/0.54    inference(avatar_component_clause,[],[f218])).
% 1.47/0.54  fof(f220,plain,(
% 1.47/0.54    spl6_35),
% 1.47/0.54    inference(avatar_split_clause,[],[f45,f218])).
% 1.47/0.54  fof(f45,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))) )),
% 1.47/0.54    inference(equality_resolution,[],[f27])).
% 1.47/0.54  fof(f27,plain,(
% 1.47/0.54    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~v1_pre_topc(X3) | ~m1_pre_topc(X3,X0) | u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3) )),
% 1.47/0.54    inference(cnf_transformation,[],[f12])).
% 1.47/0.54  fof(f12,plain,(
% 1.47/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.54    inference(flattening,[],[f11])).
% 1.47/0.54  fof(f11,plain,(
% 1.47/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.54    inference(ennf_transformation,[],[f4])).
% 1.47/0.54  fof(f4,axiom,(
% 1.47/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 1.47/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).
% 1.47/0.54  fof(f196,plain,(
% 1.47/0.54    spl6_32),
% 1.47/0.54    inference(avatar_split_clause,[],[f39,f194])).
% 1.47/0.54  fof(f39,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 1.47/0.54    inference(cnf_transformation,[],[f2])).
% 1.47/0.54  fof(f2,axiom,(
% 1.47/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.47/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.47/0.54  fof(f192,plain,(
% 1.47/0.54    spl6_31 | ~spl6_13 | ~spl6_24),
% 1.47/0.54    inference(avatar_split_clause,[],[f161,f151,f99,f190])).
% 1.47/0.54  fof(f151,plain,(
% 1.47/0.54    spl6_24 <=> ! [X1,X0] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,X1)))),
% 1.47/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.47/0.54  fof(f161,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,X1)) | m1_subset_1(X0,X1)) ) | (~spl6_13 | ~spl6_24)),
% 1.47/0.54    inference(resolution,[],[f152,f100])).
% 1.47/0.54  fof(f152,plain,(
% 1.47/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,X1))) ) | ~spl6_24),
% 1.47/0.54    inference(avatar_component_clause,[],[f151])).
% 1.47/0.54  fof(f183,plain,(
% 1.47/0.54    spl6_29),
% 1.47/0.54    inference(avatar_split_clause,[],[f36,f181])).
% 1.47/0.54  fof(f36,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f15])).
% 1.47/0.54  fof(f15,plain,(
% 1.47/0.54    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.54    inference(flattening,[],[f14])).
% 1.47/0.54  fof(f14,plain,(
% 1.47/0.54    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.54    inference(ennf_transformation,[],[f5])).
% 1.47/0.54  fof(f5,axiom,(
% 1.47/0.54    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 1.47/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 1.47/0.54  fof(f178,plain,(
% 1.47/0.54    spl6_28),
% 1.47/0.54    inference(avatar_split_clause,[],[f35,f176])).
% 1.47/0.54  fof(f35,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v1_pre_topc(k1_tsep_1(X0,X1,X2))) )),
% 1.47/0.54    inference(cnf_transformation,[],[f15])).
% 1.47/0.54  fof(f174,plain,(
% 1.47/0.54    spl6_27),
% 1.47/0.54    inference(avatar_split_clause,[],[f34,f172])).
% 1.47/0.54  fof(f34,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~v2_struct_0(k1_tsep_1(X0,X1,X2))) )),
% 1.47/0.54    inference(cnf_transformation,[],[f15])).
% 1.47/0.54  fof(f157,plain,(
% 1.47/0.54    spl6_25),
% 1.47/0.54    inference(avatar_split_clause,[],[f38,f155])).
% 1.47/0.54  fof(f38,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 1.47/0.54    inference(cnf_transformation,[],[f2])).
% 1.47/0.54  fof(f153,plain,(
% 1.47/0.54    spl6_24 | ~spl6_22),
% 1.47/0.54    inference(avatar_split_clause,[],[f143,f139,f151])).
% 1.47/0.54  fof(f143,plain,(
% 1.47/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,X1))) ) | ~spl6_22),
% 1.47/0.54    inference(factoring,[],[f140])).
% 1.47/0.54  fof(f141,plain,(
% 1.47/0.54    spl6_22),
% 1.47/0.54    inference(avatar_split_clause,[],[f48,f139])).
% 1.47/0.54  fof(f48,plain,(
% 1.47/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 1.47/0.54    inference(equality_resolution,[],[f40])).
% 1.47/0.54  fof(f40,plain,(
% 1.47/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.47/0.54    inference(cnf_transformation,[],[f2])).
% 1.47/0.54  fof(f122,plain,(
% 1.47/0.54    spl6_18),
% 1.47/0.54    inference(avatar_split_clause,[],[f47,f120])).
% 1.47/0.54  fof(f47,plain,(
% 1.47/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 1.47/0.54    inference(equality_resolution,[],[f41])).
% 1.47/0.54  fof(f41,plain,(
% 1.47/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.47/0.54    inference(cnf_transformation,[],[f2])).
% 1.47/0.54  fof(f114,plain,(
% 1.47/0.54    spl6_16),
% 1.47/0.54    inference(avatar_split_clause,[],[f33,f112])).
% 1.47/0.54  fof(f33,plain,(
% 1.47/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f13])).
% 1.47/0.54  fof(f13,plain,(
% 1.47/0.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.47/0.54    inference(ennf_transformation,[],[f3])).
% 1.47/0.54  fof(f3,axiom,(
% 1.47/0.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.47/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.47/0.54  fof(f101,plain,(
% 1.47/0.54    spl6_13),
% 1.47/0.54    inference(avatar_split_clause,[],[f49,f99])).
% 1.47/0.54  fof(f49,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.47/0.54    inference(subsumption_resolution,[],[f32,f29])).
% 1.47/0.54  % (10304)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.47/0.54  fof(f29,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f1])).
% 1.47/0.54  fof(f1,axiom,(
% 1.47/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.47/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.47/0.54  fof(f32,plain,(
% 1.47/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f13])).
% 1.47/0.54  fof(f93,plain,(
% 1.47/0.54    spl6_11),
% 1.47/0.54    inference(avatar_split_clause,[],[f29,f91])).
% 1.47/0.54  fof(f89,plain,(
% 1.47/0.54    spl6_10),
% 1.47/0.54    inference(avatar_split_clause,[],[f18,f87])).
% 1.47/0.54  fof(f18,plain,(
% 1.47/0.54    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 1.47/0.54    inference(cnf_transformation,[],[f10])).
% 1.47/0.54  fof(f10,plain,(
% 1.47/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.47/0.54    inference(flattening,[],[f9])).
% 1.47/0.54  fof(f9,plain,(
% 1.47/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.47/0.54    inference(ennf_transformation,[],[f8])).
% 1.47/0.54  fof(f8,plain,(
% 1.47/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => X3 != X5))))))),
% 1.47/0.54    inference(rectify,[],[f7])).
% 1.47/0.54  fof(f7,negated_conjecture,(
% 1.47/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 1.47/0.54    inference(negated_conjecture,[],[f6])).
% 1.47/0.54  fof(f6,conjecture,(
% 1.47/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 1.47/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tmap_1)).
% 1.47/0.54  fof(f85,plain,(
% 1.47/0.54    ~spl6_9),
% 1.47/0.54    inference(avatar_split_clause,[],[f44,f83])).
% 1.47/0.54  fof(f44,plain,(
% 1.47/0.54    ~m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.47/0.54    inference(equality_resolution,[],[f16])).
% 1.47/0.54  fof(f16,plain,(
% 1.47/0.54    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK2)) | sK3 != X4) )),
% 1.47/0.54    inference(cnf_transformation,[],[f10])).
% 1.47/0.54  fof(f81,plain,(
% 1.47/0.54    ~spl6_8),
% 1.47/0.54    inference(avatar_split_clause,[],[f43,f79])).
% 1.47/0.54  fof(f43,plain,(
% 1.47/0.54    ~m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.47/0.54    inference(equality_resolution,[],[f17])).
% 1.47/0.54  fof(f17,plain,(
% 1.47/0.54    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK1)) | sK3 != X5) )),
% 1.47/0.54    inference(cnf_transformation,[],[f10])).
% 1.47/0.54  fof(f77,plain,(
% 1.47/0.54    spl6_7),
% 1.47/0.54    inference(avatar_split_clause,[],[f22,f75])).
% 1.47/0.54  fof(f22,plain,(
% 1.47/0.54    m1_pre_topc(sK1,sK0)),
% 1.47/0.54    inference(cnf_transformation,[],[f10])).
% 1.47/0.54  fof(f73,plain,(
% 1.47/0.54    spl6_6),
% 1.47/0.54    inference(avatar_split_clause,[],[f20,f71])).
% 1.47/0.54  fof(f20,plain,(
% 1.47/0.54    m1_pre_topc(sK2,sK0)),
% 1.47/0.54    inference(cnf_transformation,[],[f10])).
% 1.47/0.54  fof(f69,plain,(
% 1.47/0.54    spl6_5),
% 1.47/0.54    inference(avatar_split_clause,[],[f25,f67])).
% 1.47/0.54  fof(f25,plain,(
% 1.47/0.54    l1_pre_topc(sK0)),
% 1.47/0.54    inference(cnf_transformation,[],[f10])).
% 1.47/0.54  fof(f61,plain,(
% 1.47/0.54    ~spl6_3),
% 1.47/0.54    inference(avatar_split_clause,[],[f23,f59])).
% 1.47/0.54  fof(f23,plain,(
% 1.47/0.54    ~v2_struct_0(sK0)),
% 1.47/0.54    inference(cnf_transformation,[],[f10])).
% 1.47/0.54  fof(f57,plain,(
% 1.47/0.54    ~spl6_2),
% 1.47/0.54    inference(avatar_split_clause,[],[f21,f55])).
% 1.47/0.54  fof(f21,plain,(
% 1.47/0.54    ~v2_struct_0(sK1)),
% 1.47/0.54    inference(cnf_transformation,[],[f10])).
% 1.47/0.54  fof(f53,plain,(
% 1.47/0.54    ~spl6_1),
% 1.47/0.54    inference(avatar_split_clause,[],[f19,f51])).
% 1.47/0.54  fof(f19,plain,(
% 1.47/0.54    ~v2_struct_0(sK2)),
% 1.47/0.54    inference(cnf_transformation,[],[f10])).
% 1.47/0.54  % SZS output end Proof for theBenchmark
% 1.47/0.54  % (10296)------------------------------
% 1.47/0.54  % (10296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.54  % (10296)Termination reason: Refutation
% 1.47/0.54  
% 1.47/0.54  % (10296)Memory used [KB]: 10874
% 1.47/0.54  % (10296)Time elapsed: 0.099 s
% 1.47/0.54  % (10296)------------------------------
% 1.47/0.54  % (10296)------------------------------
% 1.47/0.55  % (10303)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.63/0.57  % (10298)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.63/0.57  % (10302)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.63/0.57  % (10286)Success in time 0.212 s
%------------------------------------------------------------------------------
