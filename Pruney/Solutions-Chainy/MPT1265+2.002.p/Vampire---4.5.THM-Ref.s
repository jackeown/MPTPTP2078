%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 316 expanded)
%              Number of leaves         :   40 ( 153 expanded)
%              Depth                    :    8
%              Number of atoms          :  517 (1348 expanded)
%              Number of equality atoms :   51 (  96 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f409,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f70,f75,f80,f85,f89,f95,f100,f104,f108,f112,f116,f120,f135,f145,f149,f163,f185,f198,f206,f243,f264,f276,f396,f408])).

fof(f408,plain,
    ( ~ spl3_2
    | spl3_31
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_25
    | ~ spl3_35
    | ~ spl3_36
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f402,f394,f274,f261,f203,f147,f114,f110,f240,f52])).

fof(f52,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f240,plain,
    ( spl3_31
  <=> v1_tops_1(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f110,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f114,plain,
    ( spl3_15
  <=> ! [X1,X0] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f147,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( v1_tops_1(X1,X0)
        | k2_struct_0(X0) != k2_pre_topc(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f203,plain,
    ( spl3_25
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f261,plain,
    ( spl3_35
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f274,plain,
    ( spl3_36
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f394,plain,
    ( spl3_42
  <=> ! [X0] : r1_tarski(k3_xboole_0(sK2,X0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f402,plain,
    ( v1_tops_1(k3_xboole_0(sK1,sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_25
    | ~ spl3_35
    | ~ spl3_36
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f401,f279])).

fof(f279,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl3_15
    | ~ spl3_36 ),
    inference(superposition,[],[f275,f115])).

fof(f115,plain,
    ( ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f114])).

fof(f275,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f274])).

fof(f401,plain,
    ( v1_tops_1(k3_xboole_0(sK2,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_14
    | ~ spl3_19
    | ~ spl3_25
    | ~ spl3_35
    | ~ spl3_42 ),
    inference(subsumption_resolution,[],[f267,f398])).

fof(f398,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK2,X0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_14
    | ~ spl3_42 ),
    inference(unit_resulting_resolution,[],[f395,f111])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f110])).

fof(f395,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK2,X0),k2_struct_0(sK0))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f394])).

fof(f267,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k3_xboole_0(sK2,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_19
    | ~ spl3_25
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f266,f205])).

fof(f205,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f203])).

fof(f266,plain,
    ( v1_tops_1(k3_xboole_0(sK2,sK1),sK0)
    | ~ m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_19
    | ~ spl3_35 ),
    inference(trivial_inequality_removal,[],[f265])).

fof(f265,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k3_xboole_0(sK2,sK1),sK0)
    | ~ m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_19
    | ~ spl3_35 ),
    inference(superposition,[],[f148,f263])).

fof(f263,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f261])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
        | v1_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f147])).

fof(f396,plain,
    ( spl3_42
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f199,f195,f118,f394])).

fof(f118,plain,
    ( spl3_16
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k3_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f195,plain,
    ( spl3_24
  <=> r1_tarski(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f199,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK2,X0),k2_struct_0(sK0))
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(unit_resulting_resolution,[],[f197,f119])).

fof(f119,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k3_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f118])).

fof(f197,plain,
    ( r1_tarski(sK2,k2_struct_0(sK0))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f195])).

fof(f276,plain,
    ( spl3_36
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f130,f114,f102,f274])).

fof(f102,plain,
    ( spl3_12
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f130,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(superposition,[],[f115,f103])).

fof(f103,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f102])).

fof(f264,plain,
    ( spl3_35
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f180,f161,f143,f133,f97,f93,f77,f72,f67,f62,f57,f52,f47,f261])).

fof(f47,plain,
    ( spl3_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f57,plain,
    ( spl3_3
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f62,plain,
    ( spl3_4
  <=> v1_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f67,plain,
    ( spl3_5
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f72,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f77,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f93,plain,
    ( spl3_10
  <=> ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f97,plain,
    ( spl3_11
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f133,plain,
    ( spl3_17
  <=> ! [X1,X0,X2] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

% (15010)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f143,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
        | ~ v1_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f161,plain,
    ( spl3_21
  <=> ! [X1,X0,X2] :
        ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
        | ~ v3_pre_topc(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f180,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f179,f151])).

fof(f151,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f54,f64,f79,f144])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
        | ~ v1_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f143])).

fof(f79,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f64,plain,
    ( v1_tops_1(sK2,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f54,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f179,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_17
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f178,f140])).

fof(f140,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(k2_struct_0(sK0),X0,sK1)
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f136,f128])).

fof(f128,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f99,f94])).

fof(f94,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_struct_0(X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f93])).

fof(f99,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f136,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f74,f134])).

fof(f134,plain,
    ( ! [X2,X0,X1] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f133])).

fof(f74,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f178,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f164,f128])).

fof(f164,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_21 ),
    inference(unit_resulting_resolution,[],[f49,f54,f69,f59,f74,f79,f162])).

fof(f162,plain,
    ( ! [X2,X0,X1] :
        ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
        | ~ v3_pre_topc(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f161])).

fof(f59,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f69,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f49,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f243,plain,
    ( ~ spl3_31
    | spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_14
    | ~ spl3_17
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f201,f195,f133,f110,f97,f93,f82,f240])).

fof(f82,plain,
    ( spl3_8
  <=> v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f201,plain,
    ( ~ v1_tops_1(k3_xboole_0(sK1,sK2),sK0)
    | spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_14
    | ~ spl3_17
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f141,f200])).

fof(f200,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_14
    | ~ spl3_24 ),
    inference(unit_resulting_resolution,[],[f197,f111])).

fof(f141,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v1_tops_1(k3_xboole_0(sK1,sK2),sK0)
    | spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f138,f128])).

fof(f138,plain,
    ( ~ v1_tops_1(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_8
    | ~ spl3_17 ),
    inference(superposition,[],[f84,f134])).

fof(f84,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f206,plain,
    ( spl3_25
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f128,f97,f93,f203])).

fof(f198,plain,
    ( spl3_24
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f186,f182,f97,f93,f195])).

fof(f182,plain,
    ( spl3_22
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f186,plain,
    ( r1_tarski(sK2,k2_struct_0(sK0))
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f184,f128])).

fof(f184,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f182])).

fof(f185,plain,
    ( spl3_22
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f125,f106,f77,f182])).

fof(f106,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f125,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f79,f107])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f106])).

fof(f163,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f39,f161])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

% (15001)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f9,axiom,(
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

fof(f149,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f38,f147])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f145,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f37,f143])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f135,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f45,f133])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f120,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f44,f118])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f116,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f41,f114])).

fof(f41,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

% (14996)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f112,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f43,f110])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f108,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f42,f106])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f104,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f40,f102])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f100,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f90,f87,f52,f97])).

fof(f87,plain,
    ( spl3_9
  <=> ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f90,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f54,f88])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f95,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f35,f93])).

fof(f35,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f89,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f36,f87])).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f85,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f34,f82])).

fof(f34,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_pre_topc(sK2,sK0)
    & v1_tops_1(sK2,sK0)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_pre_topc(X2,X0)
                & v1_tops_1(X2,X0)
                & v1_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v3_pre_topc(X2,sK0)
              & v1_tops_1(X2,sK0)
              & v1_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v3_pre_topc(X2,sK0)
            & v1_tops_1(X2,sK0)
            & v1_tops_1(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v3_pre_topc(X2,sK0)
          & v1_tops_1(X2,sK0)
          & v1_tops_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v3_pre_topc(X2,sK0)
        & v1_tops_1(X2,sK0)
        & v1_tops_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v3_pre_topc(sK2,sK0)
      & v1_tops_1(sK2,sK0)
      & v1_tops_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v1_tops_1(X2,X0)
                    & v1_tops_1(X1,X0) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X2,X0)
                  & v1_tops_1(X2,X0)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_tops_1)).

fof(f80,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f30,f77])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f29,f72])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f33,f67])).

fof(f33,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f32,f62])).

fof(f32,plain,(
    v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f31,f57])).

fof(f31,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f28,f52])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f27,f47])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:44:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (15005)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (15000)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (15007)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (14997)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (15000)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f409,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f70,f75,f80,f85,f89,f95,f100,f104,f108,f112,f116,f120,f135,f145,f149,f163,f185,f198,f206,f243,f264,f276,f396,f408])).
% 0.22/0.48  fof(f408,plain,(
% 0.22/0.48    ~spl3_2 | spl3_31 | ~spl3_14 | ~spl3_15 | ~spl3_19 | ~spl3_25 | ~spl3_35 | ~spl3_36 | ~spl3_42),
% 0.22/0.48    inference(avatar_split_clause,[],[f402,f394,f274,f261,f203,f147,f114,f110,f240,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    spl3_2 <=> l1_pre_topc(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f240,plain,(
% 0.22/0.48    spl3_31 <=> v1_tops_1(k3_xboole_0(sK1,sK2),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    spl3_14 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    spl3_15 <=> ! [X1,X0] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.48  fof(f147,plain,(
% 0.22/0.48    spl3_19 <=> ! [X1,X0] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.48  fof(f203,plain,(
% 0.22/0.48    spl3_25 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.48  fof(f261,plain,(
% 0.22/0.48    spl3_35 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.22/0.48  fof(f274,plain,(
% 0.22/0.48    spl3_36 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.48  fof(f394,plain,(
% 0.22/0.48    spl3_42 <=> ! [X0] : r1_tarski(k3_xboole_0(sK2,X0),k2_struct_0(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.22/0.48  fof(f402,plain,(
% 0.22/0.48    v1_tops_1(k3_xboole_0(sK1,sK2),sK0) | ~l1_pre_topc(sK0) | (~spl3_14 | ~spl3_15 | ~spl3_19 | ~spl3_25 | ~spl3_35 | ~spl3_36 | ~spl3_42)),
% 0.22/0.48    inference(forward_demodulation,[],[f401,f279])).
% 0.22/0.48  fof(f279,plain,(
% 0.22/0.48    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | (~spl3_15 | ~spl3_36)),
% 0.22/0.48    inference(superposition,[],[f275,f115])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) ) | ~spl3_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f114])).
% 0.22/0.48  fof(f275,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | ~spl3_36),
% 0.22/0.48    inference(avatar_component_clause,[],[f274])).
% 0.22/0.48  fof(f401,plain,(
% 0.22/0.48    v1_tops_1(k3_xboole_0(sK2,sK1),sK0) | ~l1_pre_topc(sK0) | (~spl3_14 | ~spl3_19 | ~spl3_25 | ~spl3_35 | ~spl3_42)),
% 0.22/0.48    inference(subsumption_resolution,[],[f267,f398])).
% 0.22/0.48  fof(f398,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k3_xboole_0(sK2,X0),k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl3_14 | ~spl3_42)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f395,f111])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f110])).
% 0.22/0.48  fof(f395,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k3_xboole_0(sK2,X0),k2_struct_0(sK0))) ) | ~spl3_42),
% 0.22/0.48    inference(avatar_component_clause,[],[f394])).
% 0.22/0.48  fof(f267,plain,(
% 0.22/0.48    ~m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k3_xboole_0(sK2,sK1),sK0) | ~l1_pre_topc(sK0) | (~spl3_19 | ~spl3_25 | ~spl3_35)),
% 0.22/0.48    inference(forward_demodulation,[],[f266,f205])).
% 0.22/0.48  fof(f205,plain,(
% 0.22/0.48    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_25),
% 0.22/0.48    inference(avatar_component_clause,[],[f203])).
% 0.22/0.48  fof(f266,plain,(
% 0.22/0.48    v1_tops_1(k3_xboole_0(sK2,sK1),sK0) | ~m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_19 | ~spl3_35)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f265])).
% 0.22/0.48  fof(f265,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k3_xboole_0(sK2,sK1),sK0) | ~m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_19 | ~spl3_35)),
% 0.22/0.48    inference(superposition,[],[f148,f263])).
% 0.22/0.48  fof(f263,plain,(
% 0.22/0.48    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) | ~spl3_35),
% 0.22/0.48    inference(avatar_component_clause,[],[f261])).
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_19),
% 0.22/0.48    inference(avatar_component_clause,[],[f147])).
% 0.22/0.48  fof(f396,plain,(
% 0.22/0.48    spl3_42 | ~spl3_16 | ~spl3_24),
% 0.22/0.48    inference(avatar_split_clause,[],[f199,f195,f118,f394])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    spl3_16 <=> ! [X1,X0,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.48  fof(f195,plain,(
% 0.22/0.48    spl3_24 <=> r1_tarski(sK2,k2_struct_0(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.48  fof(f199,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k3_xboole_0(sK2,X0),k2_struct_0(sK0))) ) | (~spl3_16 | ~spl3_24)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f197,f119])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) ) | ~spl3_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f118])).
% 0.22/0.48  fof(f197,plain,(
% 0.22/0.48    r1_tarski(sK2,k2_struct_0(sK0)) | ~spl3_24),
% 0.22/0.48    inference(avatar_component_clause,[],[f195])).
% 0.22/0.48  fof(f276,plain,(
% 0.22/0.48    spl3_36 | ~spl3_12 | ~spl3_15),
% 0.22/0.48    inference(avatar_split_clause,[],[f130,f114,f102,f274])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    spl3_12 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | (~spl3_12 | ~spl3_15)),
% 0.22/0.48    inference(superposition,[],[f115,f103])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl3_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f102])).
% 0.22/0.48  fof(f264,plain,(
% 0.22/0.48    spl3_35 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_17 | ~spl3_18 | ~spl3_21),
% 0.22/0.48    inference(avatar_split_clause,[],[f180,f161,f143,f133,f97,f93,f77,f72,f67,f62,f57,f52,f47,f261])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    spl3_1 <=> v2_pre_topc(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    spl3_3 <=> v1_tops_1(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl3_4 <=> v1_tops_1(sK2,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl3_5 <=> v3_pre_topc(sK2,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    spl3_10 <=> ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    spl3_11 <=> l1_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    spl3_17 <=> ! [X1,X0,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.48  % (15010)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    spl3_18 <=> ! [X1,X0] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.48  fof(f161,plain,(
% 0.22/0.48    spl3_21 <=> ! [X1,X0,X2] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.48  fof(f180,plain,(
% 0.22/0.48    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_17 | ~spl3_18 | ~spl3_21)),
% 0.22/0.48    inference(forward_demodulation,[],[f179,f151])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    k2_struct_0(sK0) = k2_pre_topc(sK0,sK2) | (~spl3_2 | ~spl3_4 | ~spl3_7 | ~spl3_18)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f54,f64,f79,f144])).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_18),
% 0.22/0.48    inference(avatar_component_clause,[],[f143])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f77])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    v1_tops_1(sK2,sK0) | ~spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f62])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    l1_pre_topc(sK0) | ~spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f52])).
% 0.22/0.48  fof(f179,plain,(
% 0.22/0.48    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_17 | ~spl3_21)),
% 0.22/0.48    inference(forward_demodulation,[],[f178,f140])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    ( ! [X0] : (k3_xboole_0(X0,sK1) = k9_subset_1(k2_struct_0(sK0),X0,sK1)) ) | (~spl3_6 | ~spl3_10 | ~spl3_11 | ~spl3_17)),
% 0.22/0.49    inference(forward_demodulation,[],[f136,f128])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl3_10 | ~spl3_11)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f99,f94])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) ) | ~spl3_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f93])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    l1_struct_0(sK0) | ~spl3_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f97])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)) ) | (~spl3_6 | ~spl3_17)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f74,f134])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f133])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f72])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_10 | ~spl3_11 | ~spl3_21)),
% 0.22/0.49    inference(forward_demodulation,[],[f164,f128])).
% 0.22/0.49  fof(f164,plain,(
% 0.22/0.49    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_21)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f49,f54,f69,f59,f74,f79,f162])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f161])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    v1_tops_1(sK1,sK0) | ~spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f57])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    v3_pre_topc(sK2,sK0) | ~spl3_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f67])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    v2_pre_topc(sK0) | ~spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f47])).
% 0.22/0.49  fof(f243,plain,(
% 0.22/0.49    ~spl3_31 | spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_14 | ~spl3_17 | ~spl3_24),
% 0.22/0.49    inference(avatar_split_clause,[],[f201,f195,f133,f110,f97,f93,f82,f240])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    spl3_8 <=> v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.49  fof(f201,plain,(
% 0.22/0.49    ~v1_tops_1(k3_xboole_0(sK1,sK2),sK0) | (spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_14 | ~spl3_17 | ~spl3_24)),
% 0.22/0.49    inference(subsumption_resolution,[],[f141,f200])).
% 0.22/0.49  fof(f200,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_14 | ~spl3_24)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f197,f111])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(k3_xboole_0(sK1,sK2),sK0) | (spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_17)),
% 0.22/0.49    inference(forward_demodulation,[],[f138,f128])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    ~v1_tops_1(k3_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_8 | ~spl3_17)),
% 0.22/0.49    inference(superposition,[],[f84,f134])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f82])).
% 0.22/0.49  fof(f206,plain,(
% 0.22/0.49    spl3_25 | ~spl3_10 | ~spl3_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f128,f97,f93,f203])).
% 0.22/0.49  fof(f198,plain,(
% 0.22/0.49    spl3_24 | ~spl3_10 | ~spl3_11 | ~spl3_22),
% 0.22/0.49    inference(avatar_split_clause,[],[f186,f182,f97,f93,f195])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    spl3_22 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    r1_tarski(sK2,k2_struct_0(sK0)) | (~spl3_10 | ~spl3_11 | ~spl3_22)),
% 0.22/0.49    inference(forward_demodulation,[],[f184,f128])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f182])).
% 0.22/0.49  fof(f185,plain,(
% 0.22/0.49    spl3_22 | ~spl3_7 | ~spl3_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f125,f106,f77,f182])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    spl3_13 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    r1_tarski(sK2,u1_struct_0(sK0)) | (~spl3_7 | ~spl3_13)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f79,f107])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl3_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f106])).
% 0.22/0.49  fof(f163,plain,(
% 0.22/0.49    spl3_21),
% 0.22/0.49    inference(avatar_split_clause,[],[f39,f161])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((! [X2] : ((k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  % (15001)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    spl3_19),
% 0.22/0.49    inference(avatar_split_clause,[],[f38,f147])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    spl3_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f143])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    spl3_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f45,f133])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    spl3_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f44,f118])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    spl3_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f41,f114])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  % (14996)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    spl3_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f43,f110])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.49    inference(nnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    spl3_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f42,f106])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    spl3_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f40,f102])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    spl3_11 | ~spl3_2 | ~spl3_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f90,f87,f52,f97])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    spl3_9 <=> ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    l1_struct_0(sK0) | (~spl3_2 | ~spl3_9)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f54,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) ) | ~spl3_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f87])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    spl3_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f93])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl3_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f87])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ~spl3_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f82])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ((~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f23,f22,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f10])).
% 0.22/0.49  fof(f10,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_tops_1)).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    spl3_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f77])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    spl3_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f72])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f67])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    v3_pre_topc(sK2,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f62])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    v1_tops_1(sK2,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f57])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    v1_tops_1(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f28,f52])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f27,f47])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    v2_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (15000)------------------------------
% 0.22/0.49  % (15000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (15000)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (15000)Memory used [KB]: 6396
% 0.22/0.49  % (15000)Time elapsed: 0.060 s
% 0.22/0.49  % (15000)------------------------------
% 0.22/0.49  % (15000)------------------------------
% 0.22/0.49  % (14999)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (14994)Success in time 0.123 s
%------------------------------------------------------------------------------
