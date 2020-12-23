%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 306 expanded)
%              Number of leaves         :   43 ( 141 expanded)
%              Depth                    :    8
%              Number of atoms          :  548 (1021 expanded)
%              Number of equality atoms :   99 ( 190 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f904,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f56,f60,f64,f68,f72,f76,f84,f88,f92,f109,f113,f125,f129,f133,f137,f141,f154,f162,f166,f173,f178,f192,f196,f207,f213,f221,f266,f289,f318,f329,f766,f868,f899])).

fof(f899,plain,
    ( ~ spl4_27
    | spl4_44
    | ~ spl4_46
    | ~ spl4_95 ),
    inference(avatar_contradiction_clause,[],[f898])).

fof(f898,plain,
    ( $false
    | ~ spl4_27
    | spl4_44
    | ~ spl4_46
    | ~ spl4_95 ),
    inference(trivial_inequality_removal,[],[f897])).

fof(f897,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,sK2)
    | ~ spl4_27
    | spl4_44
    | ~ spl4_46
    | ~ spl4_95 ),
    inference(backward_demodulation,[],[f317,f894])).

fof(f894,plain,
    ( sK2 = k3_xboole_0(sK2,k2_struct_0(sK0))
    | ~ spl4_27
    | ~ spl4_46
    | ~ spl4_95 ),
    inference(subsumption_resolution,[],[f893,f328])).

fof(f328,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(X0,X1,X0),X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl4_46
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r2_hidden(sK3(X0,X1,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f893,plain,
    ( sK2 = k3_xboole_0(sK2,k2_struct_0(sK0))
    | r2_hidden(sK3(sK2,k2_struct_0(sK0),sK2),k2_struct_0(sK0))
    | ~ spl4_27
    | ~ spl4_95 ),
    inference(duplicate_literal_removal,[],[f885])).

fof(f885,plain,
    ( sK2 = k3_xboole_0(sK2,k2_struct_0(sK0))
    | r2_hidden(sK3(sK2,k2_struct_0(sK0),sK2),k2_struct_0(sK0))
    | sK2 = k3_xboole_0(sK2,k2_struct_0(sK0))
    | ~ spl4_27
    | ~ spl4_95 ),
    inference(resolution,[],[f867,f165])).

fof(f165,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK3(X0,X1,X2),X2)
        | r2_hidden(sK3(X0,X1,X2),X1)
        | k3_xboole_0(X0,X1) = X2 )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl4_27
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK3(X0,X1,X2),X1)
        | r2_hidden(sK3(X0,X1,X2),X2)
        | k3_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f867,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK3(X3,k2_struct_0(sK0),X3),sK2)
        | k3_xboole_0(X3,k2_struct_0(sK0)) = X3 )
    | ~ spl4_95 ),
    inference(avatar_component_clause,[],[f866])).

fof(f866,plain,
    ( spl4_95
  <=> ! [X3] :
        ( ~ r2_hidden(sK3(X3,k2_struct_0(sK0),X3),sK2)
        | k3_xboole_0(X3,k2_struct_0(sK0)) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_95])])).

fof(f317,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK2,k2_struct_0(sK0)))
    | spl4_44 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl4_44
  <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK2,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f868,plain,
    ( spl4_95
    | ~ spl4_19
    | ~ spl4_88 ),
    inference(avatar_split_clause,[],[f773,f764,f127,f866])).

fof(f127,plain,
    ( spl4_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f764,plain,
    ( spl4_88
  <=> ! [X5,X4,X6] :
        ( k3_xboole_0(X4,X5) = X4
        | ~ r2_hidden(sK3(X4,X5,X4),X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f773,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK3(X3,k2_struct_0(sK0),X3),sK2)
        | k3_xboole_0(X3,k2_struct_0(sK0)) = X3 )
    | ~ spl4_19
    | ~ spl4_88 ),
    inference(resolution,[],[f765,f128])).

fof(f128,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f127])).

fof(f765,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
        | ~ r2_hidden(sK3(X4,X5,X4),X6)
        | k3_xboole_0(X4,X5) = X4 )
    | ~ spl4_88 ),
    inference(avatar_component_clause,[],[f764])).

fof(f766,plain,
    ( spl4_88
    | ~ spl4_16
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f338,f327,f111,f764])).

fof(f111,plain,
    ( spl4_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ r2_hidden(X2,X1)
        | r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f338,plain,
    ( ! [X6,X4,X5] :
        ( k3_xboole_0(X4,X5) = X4
        | ~ r2_hidden(sK3(X4,X5,X4),X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) )
    | ~ spl4_16
    | ~ spl4_46 ),
    inference(resolution,[],[f328,f112])).

fof(f112,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f111])).

fof(f329,plain,
    ( spl4_46
    | ~ spl4_26
    | ~ spl4_29
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f224,f211,f176,f160,f327])).

fof(f160,plain,
    ( spl4_26
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK3(X0,X1,X2),X0)
        | r2_hidden(sK3(X0,X1,X2),X2)
        | k3_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f176,plain,
    ( spl4_29
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK3(X0,X1,X2),X0)
        | ~ r2_hidden(sK3(X0,X1,X2),X1)
        | ~ r2_hidden(sK3(X0,X1,X2),X2)
        | k3_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f211,plain,
    ( spl4_33
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(X0,X1,X0),X0)
        | k3_xboole_0(X0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f224,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r2_hidden(sK3(X0,X1,X0),X1) )
    | ~ spl4_26
    | ~ spl4_29
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f223,f161])).

fof(f161,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK3(X0,X1,X2),X2)
        | r2_hidden(sK3(X0,X1,X2),X0)
        | k3_xboole_0(X0,X1) = X2 )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f160])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r2_hidden(sK3(X0,X1,X0),X1)
        | ~ r2_hidden(sK3(X0,X1,X0),X0) )
    | ~ spl4_29
    | ~ spl4_33 ),
    inference(duplicate_literal_removal,[],[f222])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r2_hidden(sK3(X0,X1,X0),X1)
        | ~ r2_hidden(sK3(X0,X1,X0),X0)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl4_29
    | ~ spl4_33 ),
    inference(resolution,[],[f212,f177])).

fof(f177,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK3(X0,X1,X2),X2)
        | ~ r2_hidden(sK3(X0,X1,X2),X1)
        | ~ r2_hidden(sK3(X0,X1,X2),X0)
        | k3_xboole_0(X0,X1) = X2 )
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f176])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1,X0),X0)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f211])).

fof(f318,plain,
    ( ~ spl4_44
    | spl4_21
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f297,f287,f135,f316])).

fof(f135,plain,
    ( spl4_21
  <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f287,plain,
    ( spl4_42
  <=> k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k3_xboole_0(sK2,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f297,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK2,k2_struct_0(sK0)))
    | spl4_21
    | ~ spl4_42 ),
    inference(superposition,[],[f136,f288])).

fof(f288,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k3_xboole_0(sK2,k2_struct_0(sK0)))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f287])).

fof(f136,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f135])).

fof(f289,plain,
    ( spl4_42
    | ~ spl4_10
    | ~ spl4_22
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f273,f264,f139,f86,f287])).

fof(f86,plain,
    ( spl4_10
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f139,plain,
    ( spl4_22
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f264,plain,
    ( spl4_39
  <=> k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f273,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k3_xboole_0(sK2,k2_struct_0(sK0)))
    | ~ spl4_10
    | ~ spl4_22
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f271,f87])).

fof(f87,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f86])).

fof(f271,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k3_xboole_0(sK2,k2_struct_0(sK0)))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_22
    | ~ spl4_39 ),
    inference(superposition,[],[f265,f140])).

fof(f140,plain,
    ( ! [X2,X0,X1] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f139])).

fof(f265,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0)))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f264])).

fof(f266,plain,
    ( spl4_39
    | ~ spl4_18
    | ~ spl4_30
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f228,f219,f190,f123,f264])).

fof(f123,plain,
    ( spl4_18
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f190,plain,
    ( spl4_30
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f219,plain,
    ( spl4_35
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f228,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0)))
    | ~ spl4_18
    | ~ spl4_30
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f226,f191])).

fof(f191,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f190])).

fof(f226,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1)))
    | ~ spl4_18
    | ~ spl4_35 ),
    inference(resolution,[],[f220,f124])).

fof(f124,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f123])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0)) )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f219])).

fof(f221,plain,
    ( spl4_35
    | ~ spl4_3
    | ~ spl4_19
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f209,f205,f127,f58,f219])).

fof(f58,plain,
    ( spl4_3
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f205,plain,
    ( spl4_32
  <=> ! [X1,X0] :
        ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0)) )
    | ~ spl4_3
    | ~ spl4_19
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f208,f128])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0)) )
    | ~ spl4_3
    | ~ spl4_32 ),
    inference(resolution,[],[f206,f59])).

fof(f59,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) )
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f205])).

fof(f213,plain,
    ( spl4_33
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f169,f160,f211])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1,X0),X0)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl4_26 ),
    inference(factoring,[],[f161])).

fof(f207,plain,
    ( spl4_32
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_20
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f201,f194,f131,f54,f50,f205])).

fof(f50,plain,
    ( spl4_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f54,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f131,plain,
    ( spl4_20
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f194,plain,
    ( spl4_31
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_20
    | ~ spl4_31 ),
    inference(forward_demodulation,[],[f200,f132])).

fof(f132,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f131])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_20
    | ~ spl4_31 ),
    inference(forward_demodulation,[],[f199,f132])).

fof(f199,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_20
    | ~ spl4_31 ),
    inference(forward_demodulation,[],[f198,f132])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f197,f55])).

fof(f55,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl4_1
    | ~ spl4_31 ),
    inference(resolution,[],[f195,f51])).

fof(f51,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f195,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f194])).

fof(f196,plain,(
    spl4_31 ),
    inference(avatar_split_clause,[],[f35,f194])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).

fof(f192,plain,
    ( spl4_30
    | ~ spl4_4
    | ~ spl4_18
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f180,f171,f123,f62,f190])).

fof(f62,plain,
    ( spl4_4
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f171,plain,
    ( spl4_28
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
        | ~ v1_tops_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f180,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_18
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f179,f124])).

fof(f179,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(resolution,[],[f172,f63])).

fof(f63,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f171])).

fof(f178,plain,(
    spl4_29 ),
    inference(avatar_split_clause,[],[f39,f176])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f173,plain,
    ( spl4_28
    | ~ spl4_2
    | ~ spl4_20
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f168,f152,f131,f54,f171])).

fof(f152,plain,
    ( spl4_24
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_struct_0(X0) = k2_pre_topc(X0,X1)
        | ~ v1_tops_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f168,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
        | ~ v1_tops_1(X0,sK0) )
    | ~ spl4_2
    | ~ spl4_20
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f167,f132])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
        | ~ v1_tops_1(X0,sK0) )
    | ~ spl4_2
    | ~ spl4_24 ),
    inference(resolution,[],[f153,f55])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_struct_0(X0) = k2_pre_topc(X0,X1)
        | ~ v1_tops_1(X1,X0) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f152])).

fof(f166,plain,(
    spl4_27 ),
    inference(avatar_split_clause,[],[f41,f164])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f162,plain,(
    spl4_26 ),
    inference(avatar_split_clause,[],[f40,f160])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f154,plain,(
    spl4_24 ),
    inference(avatar_split_clause,[],[f34,f152])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f141,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f38,f139])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f137,plain,
    ( ~ spl4_21
    | ~ spl4_2
    | spl4_7
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f119,f107,f74,f54,f135])).

fof(f74,plain,
    ( spl4_7
  <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f107,plain,
    ( spl4_15
  <=> ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f119,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))
    | ~ spl4_2
    | spl4_7
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f75,f118])).

fof(f118,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_15 ),
    inference(resolution,[],[f108,f55])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f107])).

fof(f75,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f133,plain,
    ( spl4_20
    | ~ spl4_2
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f118,f107,f54,f131])).

fof(f129,plain,
    ( spl4_19
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f121,f107,f66,f54,f127])).

fof(f66,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f121,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f67,f118])).

fof(f67,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f125,plain,
    ( spl4_18
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f120,f107,f70,f54,f123])).

fof(f70,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f120,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f71,f118])).

fof(f71,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f113,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f37,f111])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f109,plain,
    ( spl4_15
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f105,f90,f82,f107])).

fof(f82,plain,
    ( spl4_9
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f90,plain,
    ( spl4_11
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f105,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(resolution,[],[f91,f83])).

fof(f83,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f92,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f31,f90])).

fof(f31,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f88,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f48,f86])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f30,f29])).

fof(f29,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f30,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f84,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f32,f82])).

fof(f32,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f76,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f24,f74])).

fof(f24,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v1_tops_1(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( v3_pre_topc(X2,X0)
                   => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

fof(f72,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f25,f70])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f22,f66])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f26,f62])).

fof(f26,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f23,f58])).

fof(f23,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f28,f54])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f27,f50])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:29:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (29698)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (29711)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (29698)Refutation not found, incomplete strategy% (29698)------------------------------
% 0.21/0.48  % (29698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (29705)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (29706)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (29698)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (29698)Memory used [KB]: 10746
% 0.21/0.48  % (29698)Time elapsed: 0.055 s
% 0.21/0.48  % (29698)------------------------------
% 0.21/0.48  % (29698)------------------------------
% 0.21/0.48  % (29705)Refutation not found, incomplete strategy% (29705)------------------------------
% 0.21/0.48  % (29705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (29705)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (29705)Memory used [KB]: 6268
% 0.21/0.48  % (29705)Time elapsed: 0.066 s
% 0.21/0.48  % (29705)------------------------------
% 0.21/0.48  % (29705)------------------------------
% 0.21/0.49  % (29706)Refutation not found, incomplete strategy% (29706)------------------------------
% 0.21/0.49  % (29706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29706)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (29706)Memory used [KB]: 10746
% 0.21/0.49  % (29706)Time elapsed: 0.065 s
% 0.21/0.49  % (29706)------------------------------
% 0.21/0.49  % (29706)------------------------------
% 0.21/0.49  % (29710)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (29696)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (29696)Refutation not found, incomplete strategy% (29696)------------------------------
% 0.21/0.49  % (29696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29696)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (29710)Refutation not found, incomplete strategy% (29710)------------------------------
% 0.21/0.49  % (29710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29696)Memory used [KB]: 10618
% 0.21/0.49  % (29696)Time elapsed: 0.074 s
% 0.21/0.49  % (29710)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  % (29696)------------------------------
% 0.21/0.49  % (29696)------------------------------
% 0.21/0.49  
% 0.21/0.49  % (29710)Memory used [KB]: 6268
% 0.21/0.49  % (29710)Time elapsed: 0.041 s
% 0.21/0.49  % (29710)------------------------------
% 0.21/0.49  % (29710)------------------------------
% 0.21/0.49  % (29700)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (29704)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (29709)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (29695)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (29702)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (29712)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (29699)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (29708)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (29701)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (29714)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (29707)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (29697)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (29713)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (29715)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (29715)Refutation not found, incomplete strategy% (29715)------------------------------
% 0.21/0.51  % (29715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29715)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29715)Memory used [KB]: 10618
% 0.21/0.51  % (29715)Time elapsed: 0.098 s
% 0.21/0.51  % (29715)------------------------------
% 0.21/0.51  % (29715)------------------------------
% 0.21/0.52  % (29703)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.53  % (29704)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f904,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f52,f56,f60,f64,f68,f72,f76,f84,f88,f92,f109,f113,f125,f129,f133,f137,f141,f154,f162,f166,f173,f178,f192,f196,f207,f213,f221,f266,f289,f318,f329,f766,f868,f899])).
% 0.21/0.53  fof(f899,plain,(
% 0.21/0.53    ~spl4_27 | spl4_44 | ~spl4_46 | ~spl4_95),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f898])).
% 0.21/0.53  fof(f898,plain,(
% 0.21/0.53    $false | (~spl4_27 | spl4_44 | ~spl4_46 | ~spl4_95)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f897])).
% 0.21/0.53  fof(f897,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,sK2) | (~spl4_27 | spl4_44 | ~spl4_46 | ~spl4_95)),
% 0.21/0.53    inference(backward_demodulation,[],[f317,f894])).
% 0.21/0.53  fof(f894,plain,(
% 0.21/0.53    sK2 = k3_xboole_0(sK2,k2_struct_0(sK0)) | (~spl4_27 | ~spl4_46 | ~spl4_95)),
% 0.21/0.53    inference(subsumption_resolution,[],[f893,f328])).
% 0.21/0.53  fof(f328,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1,X0),X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl4_46),
% 0.21/0.53    inference(avatar_component_clause,[],[f327])).
% 0.21/0.53  fof(f327,plain,(
% 0.21/0.53    spl4_46 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r2_hidden(sK3(X0,X1,X0),X1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.21/0.53  fof(f893,plain,(
% 0.21/0.53    sK2 = k3_xboole_0(sK2,k2_struct_0(sK0)) | r2_hidden(sK3(sK2,k2_struct_0(sK0),sK2),k2_struct_0(sK0)) | (~spl4_27 | ~spl4_95)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f885])).
% 0.21/0.53  fof(f885,plain,(
% 0.21/0.53    sK2 = k3_xboole_0(sK2,k2_struct_0(sK0)) | r2_hidden(sK3(sK2,k2_struct_0(sK0),sK2),k2_struct_0(sK0)) | sK2 = k3_xboole_0(sK2,k2_struct_0(sK0)) | (~spl4_27 | ~spl4_95)),
% 0.21/0.53    inference(resolution,[],[f867,f165])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | k3_xboole_0(X0,X1) = X2) ) | ~spl4_27),
% 0.21/0.53    inference(avatar_component_clause,[],[f164])).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    spl4_27 <=> ! [X1,X0,X2] : (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.53  fof(f867,plain,(
% 0.21/0.53    ( ! [X3] : (~r2_hidden(sK3(X3,k2_struct_0(sK0),X3),sK2) | k3_xboole_0(X3,k2_struct_0(sK0)) = X3) ) | ~spl4_95),
% 0.21/0.53    inference(avatar_component_clause,[],[f866])).
% 0.21/0.53  fof(f866,plain,(
% 0.21/0.53    spl4_95 <=> ! [X3] : (~r2_hidden(sK3(X3,k2_struct_0(sK0),X3),sK2) | k3_xboole_0(X3,k2_struct_0(sK0)) = X3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_95])])).
% 0.21/0.53  fof(f317,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK2,k2_struct_0(sK0))) | spl4_44),
% 0.21/0.53    inference(avatar_component_clause,[],[f316])).
% 0.21/0.53  fof(f316,plain,(
% 0.21/0.53    spl4_44 <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK2,k2_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.21/0.53  fof(f868,plain,(
% 0.21/0.53    spl4_95 | ~spl4_19 | ~spl4_88),
% 0.21/0.53    inference(avatar_split_clause,[],[f773,f764,f127,f866])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    spl4_19 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.53  fof(f764,plain,(
% 0.21/0.53    spl4_88 <=> ! [X5,X4,X6] : (k3_xboole_0(X4,X5) = X4 | ~r2_hidden(sK3(X4,X5,X4),X6) | ~m1_subset_1(X6,k1_zfmisc_1(X5)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).
% 0.21/0.53  fof(f773,plain,(
% 0.21/0.53    ( ! [X3] : (~r2_hidden(sK3(X3,k2_struct_0(sK0),X3),sK2) | k3_xboole_0(X3,k2_struct_0(sK0)) = X3) ) | (~spl4_19 | ~spl4_88)),
% 0.21/0.53    inference(resolution,[],[f765,f128])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl4_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f127])).
% 0.21/0.53  fof(f765,plain,(
% 0.21/0.53    ( ! [X6,X4,X5] : (~m1_subset_1(X6,k1_zfmisc_1(X5)) | ~r2_hidden(sK3(X4,X5,X4),X6) | k3_xboole_0(X4,X5) = X4) ) | ~spl4_88),
% 0.21/0.53    inference(avatar_component_clause,[],[f764])).
% 0.21/0.53  fof(f766,plain,(
% 0.21/0.53    spl4_88 | ~spl4_16 | ~spl4_46),
% 0.21/0.53    inference(avatar_split_clause,[],[f338,f327,f111,f764])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    spl4_16 <=> ! [X1,X0,X2] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.53  fof(f338,plain,(
% 0.21/0.53    ( ! [X6,X4,X5] : (k3_xboole_0(X4,X5) = X4 | ~r2_hidden(sK3(X4,X5,X4),X6) | ~m1_subset_1(X6,k1_zfmisc_1(X5))) ) | (~spl4_16 | ~spl4_46)),
% 0.21/0.53    inference(resolution,[],[f328,f112])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f111])).
% 0.21/0.53  fof(f329,plain,(
% 0.21/0.53    spl4_46 | ~spl4_26 | ~spl4_29 | ~spl4_33),
% 0.21/0.53    inference(avatar_split_clause,[],[f224,f211,f176,f160,f327])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    spl4_26 <=> ! [X1,X0,X2] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    spl4_29 <=> ! [X1,X0,X2] : (~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    spl4_33 <=> ! [X1,X0] : (r2_hidden(sK3(X0,X1,X0),X0) | k3_xboole_0(X0,X1) = X0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.53  fof(f224,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r2_hidden(sK3(X0,X1,X0),X1)) ) | (~spl4_26 | ~spl4_29 | ~spl4_33)),
% 0.21/0.53    inference(subsumption_resolution,[],[f223,f161])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) ) | ~spl4_26),
% 0.21/0.53    inference(avatar_component_clause,[],[f160])).
% 0.21/0.53  fof(f223,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r2_hidden(sK3(X0,X1,X0),X1) | ~r2_hidden(sK3(X0,X1,X0),X0)) ) | (~spl4_29 | ~spl4_33)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f222])).
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r2_hidden(sK3(X0,X1,X0),X1) | ~r2_hidden(sK3(X0,X1,X0),X0) | k3_xboole_0(X0,X1) = X0) ) | (~spl4_29 | ~spl4_33)),
% 0.21/0.53    inference(resolution,[],[f212,f177])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) ) | ~spl4_29),
% 0.21/0.53    inference(avatar_component_clause,[],[f176])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k3_xboole_0(X0,X1) = X0) ) | ~spl4_33),
% 0.21/0.53    inference(avatar_component_clause,[],[f211])).
% 0.21/0.53  fof(f318,plain,(
% 0.21/0.53    ~spl4_44 | spl4_21 | ~spl4_42),
% 0.21/0.53    inference(avatar_split_clause,[],[f297,f287,f135,f316])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    spl4_21 <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    spl4_42 <=> k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k3_xboole_0(sK2,k2_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.21/0.53  fof(f297,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK2,k2_struct_0(sK0))) | (spl4_21 | ~spl4_42)),
% 0.21/0.53    inference(superposition,[],[f136,f288])).
% 0.21/0.53  fof(f288,plain,(
% 0.21/0.53    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k3_xboole_0(sK2,k2_struct_0(sK0))) | ~spl4_42),
% 0.21/0.53    inference(avatar_component_clause,[],[f287])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) | spl4_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f135])).
% 0.21/0.53  fof(f289,plain,(
% 0.21/0.53    spl4_42 | ~spl4_10 | ~spl4_22 | ~spl4_39),
% 0.21/0.53    inference(avatar_split_clause,[],[f273,f264,f139,f86,f287])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl4_10 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    spl4_22 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.53  fof(f264,plain,(
% 0.21/0.53    spl4_39 <=> k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.21/0.53  fof(f273,plain,(
% 0.21/0.53    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k3_xboole_0(sK2,k2_struct_0(sK0))) | (~spl4_10 | ~spl4_22 | ~spl4_39)),
% 0.21/0.53    inference(subsumption_resolution,[],[f271,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl4_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f86])).
% 0.21/0.53  fof(f271,plain,(
% 0.21/0.53    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k3_xboole_0(sK2,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl4_22 | ~spl4_39)),
% 0.21/0.53    inference(superposition,[],[f265,f140])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl4_22),
% 0.21/0.53    inference(avatar_component_clause,[],[f139])).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0))) | ~spl4_39),
% 0.21/0.53    inference(avatar_component_clause,[],[f264])).
% 0.21/0.53  fof(f266,plain,(
% 0.21/0.53    spl4_39 | ~spl4_18 | ~spl4_30 | ~spl4_35),
% 0.21/0.53    inference(avatar_split_clause,[],[f228,f219,f190,f123,f264])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    spl4_18 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    spl4_30 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    spl4_35 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.53  fof(f228,plain,(
% 0.21/0.53    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0))) | (~spl4_18 | ~spl4_30 | ~spl4_35)),
% 0.21/0.53    inference(forward_demodulation,[],[f226,f191])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~spl4_30),
% 0.21/0.53    inference(avatar_component_clause,[],[f190])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1))) | (~spl4_18 | ~spl4_35)),
% 0.21/0.53    inference(resolution,[],[f220,f124])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl4_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f123])).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0))) ) | ~spl4_35),
% 0.21/0.53    inference(avatar_component_clause,[],[f219])).
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    spl4_35 | ~spl4_3 | ~spl4_19 | ~spl4_32),
% 0.21/0.53    inference(avatar_split_clause,[],[f209,f205,f127,f58,f219])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    spl4_3 <=> v3_pre_topc(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.53  fof(f205,plain,(
% 0.21/0.53    spl4_32 <=> ! [X1,X0] : (k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0))) ) | (~spl4_3 | ~spl4_19 | ~spl4_32)),
% 0.21/0.53    inference(subsumption_resolution,[],[f208,f128])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0))) ) | (~spl4_3 | ~spl4_32)),
% 0.21/0.53    inference(resolution,[],[f206,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    v3_pre_topc(sK2,sK0) | ~spl4_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f58])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))) ) | ~spl4_32),
% 0.21/0.53    inference(avatar_component_clause,[],[f205])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    spl4_33 | ~spl4_26),
% 0.21/0.53    inference(avatar_split_clause,[],[f169,f160,f211])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k3_xboole_0(X0,X1) = X0) ) | ~spl4_26),
% 0.21/0.53    inference(factoring,[],[f161])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    spl4_32 | ~spl4_1 | ~spl4_2 | ~spl4_20 | ~spl4_31),
% 0.21/0.53    inference(avatar_split_clause,[],[f201,f194,f131,f54,f50,f205])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    spl4_1 <=> v2_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    spl4_2 <=> l1_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    spl4_20 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    spl4_31 <=> ! [X1,X0,X2] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0)) ) | (~spl4_1 | ~spl4_2 | ~spl4_20 | ~spl4_31)),
% 0.21/0.53    inference(forward_demodulation,[],[f200,f132])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_20),
% 0.21/0.53    inference(avatar_component_clause,[],[f131])).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | (~spl4_1 | ~spl4_2 | ~spl4_20 | ~spl4_31)),
% 0.21/0.53    inference(forward_demodulation,[],[f199,f132])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | (~spl4_1 | ~spl4_2 | ~spl4_20 | ~spl4_31)),
% 0.21/0.53    inference(forward_demodulation,[],[f198,f132])).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | (~spl4_1 | ~spl4_2 | ~spl4_31)),
% 0.21/0.53    inference(subsumption_resolution,[],[f197,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    l1_pre_topc(sK0) | ~spl4_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f54])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | (~spl4_1 | ~spl4_31)),
% 0.21/0.53    inference(resolution,[],[f195,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    v2_pre_topc(sK0) | ~spl4_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f50])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) ) | ~spl4_31),
% 0.21/0.53    inference(avatar_component_clause,[],[f194])).
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    spl4_31),
% 0.21/0.53    inference(avatar_split_clause,[],[f35,f194])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    spl4_30 | ~spl4_4 | ~spl4_18 | ~spl4_28),
% 0.21/0.53    inference(avatar_split_clause,[],[f180,f171,f123,f62,f190])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    spl4_4 <=> v1_tops_1(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    spl4_28 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~v1_tops_1(X0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (~spl4_4 | ~spl4_18 | ~spl4_28)),
% 0.21/0.53    inference(subsumption_resolution,[],[f179,f124])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl4_4 | ~spl4_28)),
% 0.21/0.53    inference(resolution,[],[f172,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    v1_tops_1(sK1,sK0) | ~spl4_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f62])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_tops_1(X0,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl4_28),
% 0.21/0.53    inference(avatar_component_clause,[],[f171])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    spl4_29),
% 0.21/0.53    inference(avatar_split_clause,[],[f39,f176])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    spl4_28 | ~spl4_2 | ~spl4_20 | ~spl4_24),
% 0.21/0.53    inference(avatar_split_clause,[],[f168,f152,f131,f54,f171])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    spl4_24 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~v1_tops_1(X0,sK0)) ) | (~spl4_2 | ~spl4_20 | ~spl4_24)),
% 0.21/0.53    inference(forward_demodulation,[],[f167,f132])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~v1_tops_1(X0,sK0)) ) | (~spl4_2 | ~spl4_24)),
% 0.21/0.53    inference(resolution,[],[f153,f55])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0)) ) | ~spl4_24),
% 0.21/0.53    inference(avatar_component_clause,[],[f152])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    spl4_27),
% 0.21/0.53    inference(avatar_split_clause,[],[f41,f164])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    spl4_26),
% 0.21/0.53    inference(avatar_split_clause,[],[f40,f160])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    spl4_24),
% 0.21/0.53    inference(avatar_split_clause,[],[f34,f152])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    spl4_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f38,f139])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    ~spl4_21 | ~spl4_2 | spl4_7 | ~spl4_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f119,f107,f74,f54,f135])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    spl4_7 <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    spl4_15 <=> ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) | (~spl4_2 | spl4_7 | ~spl4_15)),
% 0.21/0.53    inference(backward_demodulation,[],[f75,f118])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl4_2 | ~spl4_15)),
% 0.21/0.53    inference(resolution,[],[f108,f55])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl4_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f107])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) | spl4_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f74])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    spl4_20 | ~spl4_2 | ~spl4_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f118,f107,f54,f131])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    spl4_19 | ~spl4_2 | ~spl4_5 | ~spl4_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f121,f107,f66,f54,f127])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl4_2 | ~spl4_5 | ~spl4_15)),
% 0.21/0.53    inference(backward_demodulation,[],[f67,f118])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f66])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    spl4_18 | ~spl4_2 | ~spl4_6 | ~spl4_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f120,f107,f70,f54,f123])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    spl4_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl4_2 | ~spl4_6 | ~spl4_15)),
% 0.21/0.53    inference(backward_demodulation,[],[f71,f118])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f70])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    spl4_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f37,f111])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    spl4_15 | ~spl4_9 | ~spl4_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f105,f90,f82,f107])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    spl4_9 <=> ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    spl4_11 <=> ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X0)) ) | (~spl4_9 | ~spl4_11)),
% 0.21/0.53    inference(resolution,[],[f91,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl4_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f82])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl4_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f90])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    spl4_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f31,f90])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    spl4_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f48,f86])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f30,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    spl4_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f32,f82])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ~spl4_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f24,f74])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((? [X2] : ((k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    spl4_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f25,f70])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    spl4_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f22,f66])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    spl4_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f26,f62])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    v1_tops_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    spl4_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f23,f58])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    v3_pre_topc(sK2,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f28,f54])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    spl4_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f27,f50])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (29704)------------------------------
% 0.21/0.53  % (29704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29704)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (29704)Memory used [KB]: 11385
% 0.21/0.53  % (29704)Time elapsed: 0.101 s
% 0.21/0.53  % (29704)------------------------------
% 0.21/0.53  % (29704)------------------------------
% 0.21/0.53  % (29694)Success in time 0.171 s
%------------------------------------------------------------------------------
