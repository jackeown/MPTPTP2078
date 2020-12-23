%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:18 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 330 expanded)
%              Number of leaves         :   36 ( 148 expanded)
%              Depth                    :   10
%              Number of atoms          :  687 (1287 expanded)
%              Number of equality atoms :   44 (  82 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f259,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f74,f78,f85,f89,f93,f97,f106,f121,f125,f129,f149,f157,f165,f169,f177,f181,f191,f192,f201,f214,f230,f236,f241,f258])).

fof(f258,plain,
    ( ~ spl4_4
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_26
    | ~ spl4_33
    | ~ spl4_34
    | spl4_36 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_26
    | ~ spl4_33
    | ~ spl4_34
    | spl4_36 ),
    inference(subsumption_resolution,[],[f249,f240])).

fof(f240,plain,
    ( ~ v1_subset_1(sK1,sK1)
    | spl4_36 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl4_36
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f249,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl4_4
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_26
    | ~ spl4_33
    | ~ spl4_34 ),
    inference(backward_demodulation,[],[f120,f248])).

fof(f248,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_26
    | ~ spl4_33
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f247,f200])).

fof(f200,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl4_33
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f247,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_26
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f246,f124])).

fof(f124,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_18
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f246,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_19
    | ~ spl4_26
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f245,f128])).

fof(f128,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl4_19
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f245,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_26
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f244,f65])).

fof(f65,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f244,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_26
    | ~ spl4_34 ),
    inference(resolution,[],[f213,f156])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ v1_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_struct_0(X0) = k2_pre_topc(X0,X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl4_26
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_struct_0(X0) = k2_pre_topc(X0,X1)
        | ~ v1_tops_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f213,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl4_34
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f120,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_17
  <=> v1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f241,plain,
    ( ~ spl4_36
    | ~ spl4_12
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f237,f228,f95,f239])).

fof(f95,plain,
    ( spl4_12
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
        | ~ v1_subset_1(X1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f228,plain,
    ( spl4_35
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f237,plain,
    ( ~ v1_subset_1(sK1,sK1)
    | ~ spl4_12
    | ~ spl4_35 ),
    inference(resolution,[],[f229,f96])).

fof(f96,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
        | ~ v1_subset_1(X1,X1) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f95])).

fof(f229,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f228])).

fof(f236,plain,
    ( spl4_9
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f235,f167,f127,f123,f80,f64,f60,f56,f83])).

fof(f83,plain,
    ( spl4_9
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f56,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f60,plain,
    ( spl4_3
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f80,plain,
    ( spl4_8
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f167,plain,
    ( spl4_29
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | v3_pre_topc(X1,X0)
        | ~ v3_tdlat_3(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f235,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f234,f124])).

fof(f234,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_19
    | ~ spl4_29 ),
    inference(backward_demodulation,[],[f233,f128])).

fof(f233,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f232,f61])).

fof(f61,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f232,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f231,f57])).

fof(f57,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f231,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f193,f65])).

fof(f193,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ spl4_8
    | ~ spl4_29 ),
    inference(resolution,[],[f81,f168])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | v3_pre_topc(X1,X0)
        | ~ v3_tdlat_3(X0) )
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f167])).

fof(f81,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f80])).

% (8953)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f230,plain,
    ( spl4_35
    | ~ spl4_4
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_26
    | ~ spl4_33
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f224,f212,f199,f155,f127,f123,f64,f228])).

fof(f224,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl4_4
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_26
    | ~ spl4_33
    | ~ spl4_34 ),
    inference(backward_demodulation,[],[f124,f219])).

fof(f219,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_26
    | ~ spl4_33
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f218,f200])).

fof(f218,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_26
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f217,f124])).

fof(f217,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_19
    | ~ spl4_26
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f216,f128])).

fof(f216,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_26
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f215,f65])).

fof(f215,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_26
    | ~ spl4_34 ),
    inference(resolution,[],[f213,f156])).

fof(f214,plain,
    ( spl4_34
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_18
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f210,f189,f123,f83,f68,f212])).

fof(f68,plain,
    ( spl4_5
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f189,plain,
    ( spl4_32
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v3_tex_2(X0,sK0)
        | v1_tops_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f210,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_18
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f209,f124])).

fof(f209,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f208,f84])).

fof(f84,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f83])).

fof(f208,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_32 ),
    inference(resolution,[],[f190,f69])).

fof(f69,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ v3_tex_2(X0,sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v1_tops_1(X0,sK0) )
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f189])).

fof(f201,plain,
    ( spl4_33
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f197,f147,f127,f123,f80,f64,f199])).

fof(f147,plain,
    ( spl4_24
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f197,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f196,f124])).

fof(f196,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_19
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f195,f128])).

fof(f195,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f194,f65])).

fof(f194,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl4_8
    | ~ spl4_24 ),
    inference(resolution,[],[f81,f148])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | k2_pre_topc(X0,X1) = X1 )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f147])).

fof(f192,plain,
    ( spl4_8
    | ~ spl4_9
    | ~ spl4_18
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f183,f175,f123,f83,f80])).

fof(f175,plain,
    ( spl4_30
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f183,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl4_9
    | ~ spl4_18
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f182,f84])).

fof(f182,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ spl4_18
    | ~ spl4_30 ),
    inference(resolution,[],[f176,f124])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v4_pre_topc(X0,sK0) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f175])).

fof(f191,plain,
    ( spl4_32
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_19
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f187,f179,f127,f64,f56,f52,f189])).

fof(f52,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f179,plain,
    ( spl4_31
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | ~ v3_tex_2(X1,X0)
        | v1_tops_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v3_tex_2(X0,sK0)
        | v1_tops_1(X0,sK0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_19
    | ~ spl4_31 ),
    inference(forward_demodulation,[],[f186,f128])).

fof(f186,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v3_tex_2(X0,sK0)
        | v1_tops_1(X0,sK0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f185,f65])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v3_tex_2(X0,sK0)
        | v1_tops_1(X0,sK0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f184,f57])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v3_tex_2(X0,sK0)
        | v1_tops_1(X0,sK0) )
    | spl4_1
    | ~ spl4_31 ),
    inference(resolution,[],[f180,f53])).

fof(f53,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | ~ v3_tex_2(X1,X0)
        | v1_tops_1(X1,X0) )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f179])).

fof(f181,plain,(
    spl4_31 ),
    inference(avatar_split_clause,[],[f39,f179])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

fof(f177,plain,
    ( spl4_30
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_19
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f173,f163,f127,f64,f60,f56,f175])).

fof(f163,plain,
    ( spl4_28
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | v4_pre_topc(X1,X0)
        | ~ v3_tdlat_3(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v4_pre_topc(X0,sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_19
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f172,f128])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v4_pre_topc(X0,sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f171,f61])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v4_pre_topc(X0,sK0)
        | ~ v3_tdlat_3(sK0) )
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f170,f65])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v4_pre_topc(X0,sK0)
        | ~ v3_tdlat_3(sK0) )
    | ~ spl4_2
    | ~ spl4_28 ),
    inference(resolution,[],[f164,f57])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | v4_pre_topc(X1,X0)
        | ~ v3_tdlat_3(X0) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f163])).

fof(f169,plain,(
    spl4_29 ),
    inference(avatar_split_clause,[],[f44,f167])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(X1,X0)
      | ~ v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f165,plain,(
    spl4_28 ),
    inference(avatar_split_clause,[],[f40,f163])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | v4_pre_topc(X1,X0)
      | ~ v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
             => v4_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tdlat_3)).

fof(f157,plain,(
    spl4_26 ),
    inference(avatar_split_clause,[],[f38,f155])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f149,plain,(
    spl4_24 ),
    inference(avatar_split_clause,[],[f36,f147])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f129,plain,
    ( spl4_19
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f115,f104,f64,f127])).

fof(f104,plain,
    ( spl4_14
  <=> ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f115,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(resolution,[],[f105,f65])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f104])).

fof(f125,plain,
    ( spl4_18
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f116,f104,f76,f64,f123])).

fof(f76,plain,
    ( spl4_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f116,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(backward_demodulation,[],[f77,f115])).

fof(f77,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f121,plain,
    ( spl4_17
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f117,f104,f72,f64,f119])).

fof(f72,plain,
    ( spl4_6
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f117,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(backward_demodulation,[],[f73,f115])).

fof(f73,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f106,plain,
    ( spl4_14
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f98,f91,f87,f104])).

fof(f87,plain,
    ( spl4_10
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f91,plain,
    ( spl4_11
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f98,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(resolution,[],[f92,f88])).

fof(f88,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f87])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f91])).

fof(f97,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f50,f95])).

fof(f50,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f93,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f33,f91])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f89,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f34,f87])).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f85,plain,
    ( spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f25,f83,f80])).

fof(f25,plain,
    ( v3_pre_topc(sK1,sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( v1_subset_1(X1,u1_struct_0(X0))
                & v3_tex_2(X1,X0)
                & ( v4_pre_topc(X1,X0)
                  | v3_pre_topc(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( v1_subset_1(X1,u1_struct_0(X0))
              & v3_tex_2(X1,X0)
              & ( v4_pre_topc(X1,X0)
                | v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).

fof(f78,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f26,f76])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f74,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f28,f72])).

fof(f28,plain,(
    v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f27,f68])).

fof(f27,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f66,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f32,f64])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f31,f60])).

fof(f31,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f30,f56])).

fof(f30,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f54,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f29,f52])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:07:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.47  % (8970)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.23/0.47  % (8962)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.23/0.48  % (8962)Refutation found. Thanks to Tanya!
% 0.23/0.48  % SZS status Theorem for theBenchmark
% 0.23/0.48  % SZS output start Proof for theBenchmark
% 0.23/0.48  fof(f259,plain,(
% 0.23/0.48    $false),
% 0.23/0.48    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f74,f78,f85,f89,f93,f97,f106,f121,f125,f129,f149,f157,f165,f169,f177,f181,f191,f192,f201,f214,f230,f236,f241,f258])).
% 0.23/0.48  fof(f258,plain,(
% 0.23/0.48    ~spl4_4 | ~spl4_17 | ~spl4_18 | ~spl4_19 | ~spl4_26 | ~spl4_33 | ~spl4_34 | spl4_36),
% 0.23/0.48    inference(avatar_contradiction_clause,[],[f257])).
% 0.23/0.48  fof(f257,plain,(
% 0.23/0.48    $false | (~spl4_4 | ~spl4_17 | ~spl4_18 | ~spl4_19 | ~spl4_26 | ~spl4_33 | ~spl4_34 | spl4_36)),
% 0.23/0.48    inference(subsumption_resolution,[],[f249,f240])).
% 0.23/0.48  fof(f240,plain,(
% 0.23/0.48    ~v1_subset_1(sK1,sK1) | spl4_36),
% 0.23/0.48    inference(avatar_component_clause,[],[f239])).
% 0.23/0.48  fof(f239,plain,(
% 0.23/0.48    spl4_36 <=> v1_subset_1(sK1,sK1)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.23/0.48  fof(f249,plain,(
% 0.23/0.48    v1_subset_1(sK1,sK1) | (~spl4_4 | ~spl4_17 | ~spl4_18 | ~spl4_19 | ~spl4_26 | ~spl4_33 | ~spl4_34)),
% 0.23/0.48    inference(backward_demodulation,[],[f120,f248])).
% 0.23/0.48  fof(f248,plain,(
% 0.23/0.48    sK1 = k2_struct_0(sK0) | (~spl4_4 | ~spl4_18 | ~spl4_19 | ~spl4_26 | ~spl4_33 | ~spl4_34)),
% 0.23/0.48    inference(forward_demodulation,[],[f247,f200])).
% 0.23/0.48  fof(f200,plain,(
% 0.23/0.48    sK1 = k2_pre_topc(sK0,sK1) | ~spl4_33),
% 0.23/0.48    inference(avatar_component_clause,[],[f199])).
% 0.23/0.48  fof(f199,plain,(
% 0.23/0.48    spl4_33 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.23/0.48  fof(f247,plain,(
% 0.23/0.48    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (~spl4_4 | ~spl4_18 | ~spl4_19 | ~spl4_26 | ~spl4_34)),
% 0.23/0.48    inference(subsumption_resolution,[],[f246,f124])).
% 0.23/0.48  fof(f124,plain,(
% 0.23/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl4_18),
% 0.23/0.48    inference(avatar_component_clause,[],[f123])).
% 0.23/0.48  fof(f123,plain,(
% 0.23/0.48    spl4_18 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.23/0.48  fof(f246,plain,(
% 0.23/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (~spl4_4 | ~spl4_19 | ~spl4_26 | ~spl4_34)),
% 0.23/0.48    inference(forward_demodulation,[],[f245,f128])).
% 0.23/0.48  fof(f128,plain,(
% 0.23/0.48    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_19),
% 0.23/0.48    inference(avatar_component_clause,[],[f127])).
% 0.23/0.48  fof(f127,plain,(
% 0.23/0.48    spl4_19 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.23/0.48  fof(f245,plain,(
% 0.23/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (~spl4_4 | ~spl4_26 | ~spl4_34)),
% 0.23/0.48    inference(subsumption_resolution,[],[f244,f65])).
% 0.23/0.48  fof(f65,plain,(
% 0.23/0.48    l1_pre_topc(sK0) | ~spl4_4),
% 0.23/0.48    inference(avatar_component_clause,[],[f64])).
% 0.23/0.48  fof(f64,plain,(
% 0.23/0.48    spl4_4 <=> l1_pre_topc(sK0)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.23/0.48  fof(f244,plain,(
% 0.23/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl4_26 | ~spl4_34)),
% 0.23/0.48    inference(resolution,[],[f213,f156])).
% 0.23/0.48  fof(f156,plain,(
% 0.23/0.48    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) ) | ~spl4_26),
% 0.23/0.48    inference(avatar_component_clause,[],[f155])).
% 0.23/0.48  fof(f155,plain,(
% 0.23/0.48    spl4_26 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.23/0.48  fof(f213,plain,(
% 0.23/0.48    v1_tops_1(sK1,sK0) | ~spl4_34),
% 0.23/0.48    inference(avatar_component_clause,[],[f212])).
% 0.23/0.48  fof(f212,plain,(
% 0.23/0.48    spl4_34 <=> v1_tops_1(sK1,sK0)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.23/0.48  fof(f120,plain,(
% 0.23/0.48    v1_subset_1(sK1,k2_struct_0(sK0)) | ~spl4_17),
% 0.23/0.48    inference(avatar_component_clause,[],[f119])).
% 0.23/0.48  fof(f119,plain,(
% 0.23/0.48    spl4_17 <=> v1_subset_1(sK1,k2_struct_0(sK0))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.23/0.48  fof(f241,plain,(
% 0.23/0.48    ~spl4_36 | ~spl4_12 | ~spl4_35),
% 0.23/0.48    inference(avatar_split_clause,[],[f237,f228,f95,f239])).
% 0.23/0.48  fof(f95,plain,(
% 0.23/0.48    spl4_12 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.23/0.48  fof(f228,plain,(
% 0.23/0.48    spl4_35 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.23/0.48  fof(f237,plain,(
% 0.23/0.48    ~v1_subset_1(sK1,sK1) | (~spl4_12 | ~spl4_35)),
% 0.23/0.48    inference(resolution,[],[f229,f96])).
% 0.23/0.48  fof(f96,plain,(
% 0.23/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) ) | ~spl4_12),
% 0.23/0.48    inference(avatar_component_clause,[],[f95])).
% 0.23/0.48  fof(f229,plain,(
% 0.23/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl4_35),
% 0.23/0.48    inference(avatar_component_clause,[],[f228])).
% 0.23/0.48  fof(f236,plain,(
% 0.23/0.48    spl4_9 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_8 | ~spl4_18 | ~spl4_19 | ~spl4_29),
% 0.23/0.48    inference(avatar_split_clause,[],[f235,f167,f127,f123,f80,f64,f60,f56,f83])).
% 0.23/0.48  fof(f83,plain,(
% 0.23/0.48    spl4_9 <=> v3_pre_topc(sK1,sK0)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.23/0.48  fof(f56,plain,(
% 0.23/0.48    spl4_2 <=> v2_pre_topc(sK0)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.23/0.48  fof(f60,plain,(
% 0.23/0.48    spl4_3 <=> v3_tdlat_3(sK0)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.23/0.48  fof(f80,plain,(
% 0.23/0.48    spl4_8 <=> v4_pre_topc(sK1,sK0)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.23/0.48  fof(f167,plain,(
% 0.23/0.48    spl4_29 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0) | ~v3_tdlat_3(X0))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.23/0.48  fof(f235,plain,(
% 0.23/0.48    v3_pre_topc(sK1,sK0) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_8 | ~spl4_18 | ~spl4_19 | ~spl4_29)),
% 0.23/0.48    inference(subsumption_resolution,[],[f234,f124])).
% 0.23/0.48  fof(f234,plain,(
% 0.23/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(sK1,sK0) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_8 | ~spl4_19 | ~spl4_29)),
% 0.23/0.48    inference(backward_demodulation,[],[f233,f128])).
% 0.23/0.48  fof(f233,plain,(
% 0.23/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_8 | ~spl4_29)),
% 0.23/0.48    inference(subsumption_resolution,[],[f232,f61])).
% 0.23/0.48  fof(f61,plain,(
% 0.23/0.48    v3_tdlat_3(sK0) | ~spl4_3),
% 0.23/0.48    inference(avatar_component_clause,[],[f60])).
% 0.23/0.48  fof(f232,plain,(
% 0.23/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0) | (~spl4_2 | ~spl4_4 | ~spl4_8 | ~spl4_29)),
% 0.23/0.48    inference(subsumption_resolution,[],[f231,f57])).
% 0.23/0.48  fof(f57,plain,(
% 0.23/0.48    v2_pre_topc(sK0) | ~spl4_2),
% 0.23/0.48    inference(avatar_component_clause,[],[f56])).
% 0.23/0.48  fof(f231,plain,(
% 0.23/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0) | (~spl4_4 | ~spl4_8 | ~spl4_29)),
% 0.23/0.48    inference(subsumption_resolution,[],[f193,f65])).
% 0.23/0.48  fof(f193,plain,(
% 0.23/0.48    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0) | (~spl4_8 | ~spl4_29)),
% 0.23/0.48    inference(resolution,[],[f81,f168])).
% 0.23/0.48  fof(f168,plain,(
% 0.23/0.48    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | v3_pre_topc(X1,X0) | ~v3_tdlat_3(X0)) ) | ~spl4_29),
% 0.23/0.48    inference(avatar_component_clause,[],[f167])).
% 0.23/0.48  fof(f81,plain,(
% 0.23/0.48    v4_pre_topc(sK1,sK0) | ~spl4_8),
% 0.23/0.48    inference(avatar_component_clause,[],[f80])).
% 0.23/0.48  % (8953)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.23/0.48  fof(f230,plain,(
% 0.23/0.48    spl4_35 | ~spl4_4 | ~spl4_18 | ~spl4_19 | ~spl4_26 | ~spl4_33 | ~spl4_34),
% 0.23/0.48    inference(avatar_split_clause,[],[f224,f212,f199,f155,f127,f123,f64,f228])).
% 0.23/0.48  fof(f224,plain,(
% 0.23/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl4_4 | ~spl4_18 | ~spl4_19 | ~spl4_26 | ~spl4_33 | ~spl4_34)),
% 0.23/0.48    inference(backward_demodulation,[],[f124,f219])).
% 0.23/0.48  fof(f219,plain,(
% 0.23/0.48    sK1 = k2_struct_0(sK0) | (~spl4_4 | ~spl4_18 | ~spl4_19 | ~spl4_26 | ~spl4_33 | ~spl4_34)),
% 0.23/0.48    inference(forward_demodulation,[],[f218,f200])).
% 0.23/0.48  fof(f218,plain,(
% 0.23/0.48    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (~spl4_4 | ~spl4_18 | ~spl4_19 | ~spl4_26 | ~spl4_34)),
% 0.23/0.48    inference(subsumption_resolution,[],[f217,f124])).
% 0.23/0.48  fof(f217,plain,(
% 0.23/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (~spl4_4 | ~spl4_19 | ~spl4_26 | ~spl4_34)),
% 0.23/0.48    inference(forward_demodulation,[],[f216,f128])).
% 0.23/0.48  fof(f216,plain,(
% 0.23/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (~spl4_4 | ~spl4_26 | ~spl4_34)),
% 0.23/0.48    inference(subsumption_resolution,[],[f215,f65])).
% 0.23/0.48  fof(f215,plain,(
% 0.23/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl4_26 | ~spl4_34)),
% 0.23/0.48    inference(resolution,[],[f213,f156])).
% 0.23/0.48  fof(f214,plain,(
% 0.23/0.48    spl4_34 | ~spl4_5 | ~spl4_9 | ~spl4_18 | ~spl4_32),
% 0.23/0.48    inference(avatar_split_clause,[],[f210,f189,f123,f83,f68,f212])).
% 0.23/0.48  fof(f68,plain,(
% 0.23/0.48    spl4_5 <=> v3_tex_2(sK1,sK0)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.23/0.48  fof(f189,plain,(
% 0.23/0.48    spl4_32 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v3_tex_2(X0,sK0) | v1_tops_1(X0,sK0))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.23/0.48  fof(f210,plain,(
% 0.23/0.48    v1_tops_1(sK1,sK0) | (~spl4_5 | ~spl4_9 | ~spl4_18 | ~spl4_32)),
% 0.23/0.48    inference(subsumption_resolution,[],[f209,f124])).
% 0.23/0.48  fof(f209,plain,(
% 0.23/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(sK1,sK0) | (~spl4_5 | ~spl4_9 | ~spl4_32)),
% 0.23/0.48    inference(subsumption_resolution,[],[f208,f84])).
% 0.23/0.48  fof(f84,plain,(
% 0.23/0.48    v3_pre_topc(sK1,sK0) | ~spl4_9),
% 0.23/0.48    inference(avatar_component_clause,[],[f83])).
% 0.23/0.48  fof(f208,plain,(
% 0.23/0.48    ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(sK1,sK0) | (~spl4_5 | ~spl4_32)),
% 0.23/0.48    inference(resolution,[],[f190,f69])).
% 0.23/0.48  fof(f69,plain,(
% 0.23/0.48    v3_tex_2(sK1,sK0) | ~spl4_5),
% 0.23/0.48    inference(avatar_component_clause,[],[f68])).
% 0.23/0.48  fof(f190,plain,(
% 0.23/0.48    ( ! [X0] : (~v3_tex_2(X0,sK0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(X0,sK0)) ) | ~spl4_32),
% 0.23/0.48    inference(avatar_component_clause,[],[f189])).
% 0.23/0.48  fof(f201,plain,(
% 0.23/0.48    spl4_33 | ~spl4_4 | ~spl4_8 | ~spl4_18 | ~spl4_19 | ~spl4_24),
% 0.23/0.48    inference(avatar_split_clause,[],[f197,f147,f127,f123,f80,f64,f199])).
% 0.23/0.48  fof(f147,plain,(
% 0.23/0.48    spl4_24 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.23/0.48  fof(f197,plain,(
% 0.23/0.48    sK1 = k2_pre_topc(sK0,sK1) | (~spl4_4 | ~spl4_8 | ~spl4_18 | ~spl4_19 | ~spl4_24)),
% 0.23/0.48    inference(subsumption_resolution,[],[f196,f124])).
% 0.23/0.48  fof(f196,plain,(
% 0.23/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1) | (~spl4_4 | ~spl4_8 | ~spl4_19 | ~spl4_24)),
% 0.23/0.48    inference(forward_demodulation,[],[f195,f128])).
% 0.23/0.48  fof(f195,plain,(
% 0.23/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1) | (~spl4_4 | ~spl4_8 | ~spl4_24)),
% 0.23/0.48    inference(subsumption_resolution,[],[f194,f65])).
% 0.23/0.48  fof(f194,plain,(
% 0.23/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | sK1 = k2_pre_topc(sK0,sK1) | (~spl4_8 | ~spl4_24)),
% 0.23/0.48    inference(resolution,[],[f81,f148])).
% 0.23/0.48  fof(f148,plain,(
% 0.23/0.48    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = X1) ) | ~spl4_24),
% 0.23/0.48    inference(avatar_component_clause,[],[f147])).
% 0.23/0.48  fof(f192,plain,(
% 0.23/0.48    spl4_8 | ~spl4_9 | ~spl4_18 | ~spl4_30),
% 0.23/0.48    inference(avatar_split_clause,[],[f183,f175,f123,f83,f80])).
% 0.23/0.48  fof(f175,plain,(
% 0.23/0.48    spl4_30 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | v4_pre_topc(X0,sK0))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.23/0.48  fof(f183,plain,(
% 0.23/0.48    v4_pre_topc(sK1,sK0) | (~spl4_9 | ~spl4_18 | ~spl4_30)),
% 0.23/0.48    inference(subsumption_resolution,[],[f182,f84])).
% 0.23/0.48  fof(f182,plain,(
% 0.23/0.48    ~v3_pre_topc(sK1,sK0) | v4_pre_topc(sK1,sK0) | (~spl4_18 | ~spl4_30)),
% 0.23/0.48    inference(resolution,[],[f176,f124])).
% 0.23/0.48  fof(f176,plain,(
% 0.23/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | v4_pre_topc(X0,sK0)) ) | ~spl4_30),
% 0.23/0.48    inference(avatar_component_clause,[],[f175])).
% 0.23/0.48  fof(f191,plain,(
% 0.23/0.48    spl4_32 | spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_19 | ~spl4_31),
% 0.23/0.48    inference(avatar_split_clause,[],[f187,f179,f127,f64,f56,f52,f189])).
% 0.23/0.48  fof(f52,plain,(
% 0.23/0.48    spl4_1 <=> v2_struct_0(sK0)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.23/0.48  fof(f179,plain,(
% 0.23/0.48    spl4_31 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~v3_tex_2(X1,X0) | v1_tops_1(X1,X0))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.23/0.48  fof(f187,plain,(
% 0.23/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v3_tex_2(X0,sK0) | v1_tops_1(X0,sK0)) ) | (spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_19 | ~spl4_31)),
% 0.23/0.48    inference(forward_demodulation,[],[f186,f128])).
% 0.23/0.48  fof(f186,plain,(
% 0.23/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v3_tex_2(X0,sK0) | v1_tops_1(X0,sK0)) ) | (spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_31)),
% 0.23/0.48    inference(subsumption_resolution,[],[f185,f65])).
% 0.23/0.48  fof(f185,plain,(
% 0.23/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v3_tex_2(X0,sK0) | v1_tops_1(X0,sK0)) ) | (spl4_1 | ~spl4_2 | ~spl4_31)),
% 0.23/0.48    inference(subsumption_resolution,[],[f184,f57])).
% 0.23/0.48  fof(f184,plain,(
% 0.23/0.48    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v3_tex_2(X0,sK0) | v1_tops_1(X0,sK0)) ) | (spl4_1 | ~spl4_31)),
% 0.23/0.48    inference(resolution,[],[f180,f53])).
% 0.23/0.48  fof(f53,plain,(
% 0.23/0.48    ~v2_struct_0(sK0) | spl4_1),
% 0.23/0.48    inference(avatar_component_clause,[],[f52])).
% 0.23/0.48  fof(f180,plain,(
% 0.23/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~v3_tex_2(X1,X0) | v1_tops_1(X1,X0)) ) | ~spl4_31),
% 0.23/0.48    inference(avatar_component_clause,[],[f179])).
% 0.23/0.48  fof(f181,plain,(
% 0.23/0.48    spl4_31),
% 0.23/0.48    inference(avatar_split_clause,[],[f39,f179])).
% 0.23/0.48  fof(f39,plain,(
% 0.23/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~v3_tex_2(X1,X0) | v1_tops_1(X1,X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f19])).
% 0.23/0.48  fof(f19,plain,(
% 0.23/0.48    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.48    inference(flattening,[],[f18])).
% 0.23/0.48  fof(f18,plain,(
% 0.23/0.48    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.23/0.48    inference(ennf_transformation,[],[f8])).
% 0.23/0.48  fof(f8,axiom,(
% 0.23/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).
% 0.23/0.48  fof(f177,plain,(
% 0.23/0.48    spl4_30 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_19 | ~spl4_28),
% 0.23/0.48    inference(avatar_split_clause,[],[f173,f163,f127,f64,f60,f56,f175])).
% 0.23/0.48  fof(f163,plain,(
% 0.23/0.48    spl4_28 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | v4_pre_topc(X1,X0) | ~v3_tdlat_3(X0))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.23/0.48  fof(f173,plain,(
% 0.23/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | v4_pre_topc(X0,sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_19 | ~spl4_28)),
% 0.23/0.48    inference(forward_demodulation,[],[f172,f128])).
% 0.23/0.48  fof(f172,plain,(
% 0.23/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | v4_pre_topc(X0,sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_28)),
% 0.23/0.48    inference(subsumption_resolution,[],[f171,f61])).
% 0.23/0.48  fof(f171,plain,(
% 0.23/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | v4_pre_topc(X0,sK0) | ~v3_tdlat_3(sK0)) ) | (~spl4_2 | ~spl4_4 | ~spl4_28)),
% 0.23/0.48    inference(subsumption_resolution,[],[f170,f65])).
% 0.23/0.48  fof(f170,plain,(
% 0.23/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | v4_pre_topc(X0,sK0) | ~v3_tdlat_3(sK0)) ) | (~spl4_2 | ~spl4_28)),
% 0.23/0.48    inference(resolution,[],[f164,f57])).
% 0.23/0.48  fof(f164,plain,(
% 0.23/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | v4_pre_topc(X1,X0) | ~v3_tdlat_3(X0)) ) | ~spl4_28),
% 0.23/0.48    inference(avatar_component_clause,[],[f163])).
% 0.23/0.48  fof(f169,plain,(
% 0.23/0.48    spl4_29),
% 0.23/0.48    inference(avatar_split_clause,[],[f44,f167])).
% 0.23/0.48  fof(f44,plain,(
% 0.23/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0) | ~v3_tdlat_3(X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f23])).
% 0.23/0.48  fof(f23,plain,(
% 0.23/0.48    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.48    inference(flattening,[],[f22])).
% 0.23/0.48  fof(f22,plain,(
% 0.23/0.48    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.48    inference(ennf_transformation,[],[f7])).
% 0.23/0.48  fof(f7,axiom,(
% 0.23/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.23/0.48  fof(f165,plain,(
% 0.23/0.48    spl4_28),
% 0.23/0.48    inference(avatar_split_clause,[],[f40,f163])).
% 0.23/0.48  fof(f40,plain,(
% 0.23/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | v4_pre_topc(X1,X0) | ~v3_tdlat_3(X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f21])).
% 0.23/0.48  fof(f21,plain,(
% 0.23/0.48    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.48    inference(flattening,[],[f20])).
% 0.23/0.48  fof(f20,plain,(
% 0.23/0.48    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.48    inference(ennf_transformation,[],[f6])).
% 0.23/0.48  fof(f6,axiom,(
% 0.23/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => v4_pre_topc(X1,X0)))))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tdlat_3)).
% 0.23/0.48  fof(f157,plain,(
% 0.23/0.48    spl4_26),
% 0.23/0.48    inference(avatar_split_clause,[],[f38,f155])).
% 0.23/0.48  fof(f38,plain,(
% 0.23/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f17])).
% 0.23/0.48  fof(f17,plain,(
% 0.23/0.48    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.48    inference(ennf_transformation,[],[f4])).
% 0.23/0.48  fof(f4,axiom,(
% 0.23/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.23/0.48  fof(f149,plain,(
% 0.23/0.48    spl4_24),
% 0.23/0.48    inference(avatar_split_clause,[],[f36,f147])).
% 0.23/0.48  fof(f36,plain,(
% 0.23/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.23/0.48    inference(cnf_transformation,[],[f16])).
% 0.23/0.48  fof(f16,plain,(
% 0.23/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.48    inference(flattening,[],[f15])).
% 0.23/0.48  fof(f15,plain,(
% 0.23/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.48    inference(ennf_transformation,[],[f3])).
% 0.23/0.48  fof(f3,axiom,(
% 0.23/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.23/0.48  fof(f129,plain,(
% 0.23/0.48    spl4_19 | ~spl4_4 | ~spl4_14),
% 0.23/0.48    inference(avatar_split_clause,[],[f115,f104,f64,f127])).
% 0.23/0.48  fof(f104,plain,(
% 0.23/0.48    spl4_14 <=> ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.23/0.48  fof(f115,plain,(
% 0.23/0.48    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl4_4 | ~spl4_14)),
% 0.23/0.48    inference(resolution,[],[f105,f65])).
% 0.23/0.48  fof(f105,plain,(
% 0.23/0.48    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl4_14),
% 0.23/0.48    inference(avatar_component_clause,[],[f104])).
% 0.23/0.48  fof(f125,plain,(
% 0.23/0.48    spl4_18 | ~spl4_4 | ~spl4_7 | ~spl4_14),
% 0.23/0.48    inference(avatar_split_clause,[],[f116,f104,f76,f64,f123])).
% 0.23/0.48  fof(f76,plain,(
% 0.23/0.48    spl4_7 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.23/0.48  fof(f116,plain,(
% 0.23/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl4_4 | ~spl4_7 | ~spl4_14)),
% 0.23/0.48    inference(backward_demodulation,[],[f77,f115])).
% 0.23/0.48  fof(f77,plain,(
% 0.23/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_7),
% 0.23/0.48    inference(avatar_component_clause,[],[f76])).
% 0.23/0.48  fof(f121,plain,(
% 0.23/0.48    spl4_17 | ~spl4_4 | ~spl4_6 | ~spl4_14),
% 0.23/0.48    inference(avatar_split_clause,[],[f117,f104,f72,f64,f119])).
% 0.23/0.48  fof(f72,plain,(
% 0.23/0.48    spl4_6 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.23/0.48  fof(f117,plain,(
% 0.23/0.48    v1_subset_1(sK1,k2_struct_0(sK0)) | (~spl4_4 | ~spl4_6 | ~spl4_14)),
% 0.23/0.48    inference(backward_demodulation,[],[f73,f115])).
% 0.23/0.48  fof(f73,plain,(
% 0.23/0.48    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_6),
% 0.23/0.48    inference(avatar_component_clause,[],[f72])).
% 0.23/0.48  fof(f106,plain,(
% 0.23/0.48    spl4_14 | ~spl4_10 | ~spl4_11),
% 0.23/0.48    inference(avatar_split_clause,[],[f98,f91,f87,f104])).
% 0.23/0.48  fof(f87,plain,(
% 0.23/0.48    spl4_10 <=> ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.23/0.48  fof(f91,plain,(
% 0.23/0.48    spl4_11 <=> ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.23/0.48  fof(f98,plain,(
% 0.23/0.48    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X0)) ) | (~spl4_10 | ~spl4_11)),
% 0.23/0.48    inference(resolution,[],[f92,f88])).
% 0.23/0.48  fof(f88,plain,(
% 0.23/0.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl4_10),
% 0.23/0.48    inference(avatar_component_clause,[],[f87])).
% 0.23/0.48  fof(f92,plain,(
% 0.23/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl4_11),
% 0.23/0.48    inference(avatar_component_clause,[],[f91])).
% 0.23/0.48  fof(f97,plain,(
% 0.23/0.48    spl4_12),
% 0.23/0.48    inference(avatar_split_clause,[],[f50,f95])).
% 0.23/0.48  fof(f50,plain,(
% 0.23/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.23/0.48    inference(equality_resolution,[],[f49])).
% 0.23/0.48  fof(f49,plain,(
% 0.23/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f24])).
% 0.23/0.48  fof(f24,plain,(
% 0.23/0.48    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.48    inference(ennf_transformation,[],[f5])).
% 0.23/0.48  fof(f5,axiom,(
% 0.23/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.23/0.48  fof(f93,plain,(
% 0.23/0.48    spl4_11),
% 0.23/0.48    inference(avatar_split_clause,[],[f33,f91])).
% 0.23/0.48  fof(f33,plain,(
% 0.23/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f13])).
% 0.23/0.48  fof(f13,plain,(
% 0.23/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.23/0.48    inference(ennf_transformation,[],[f1])).
% 0.23/0.48  fof(f1,axiom,(
% 0.23/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.23/0.48  fof(f89,plain,(
% 0.23/0.48    spl4_10),
% 0.23/0.48    inference(avatar_split_clause,[],[f34,f87])).
% 0.23/0.48  fof(f34,plain,(
% 0.23/0.48    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f14])).
% 0.23/0.48  fof(f14,plain,(
% 0.23/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.23/0.48    inference(ennf_transformation,[],[f2])).
% 0.23/0.48  fof(f2,axiom,(
% 0.23/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.23/0.48  fof(f85,plain,(
% 0.23/0.48    spl4_8 | spl4_9),
% 0.23/0.48    inference(avatar_split_clause,[],[f25,f83,f80])).
% 0.23/0.48  fof(f25,plain,(
% 0.23/0.48    v3_pre_topc(sK1,sK0) | v4_pre_topc(sK1,sK0)),
% 0.23/0.48    inference(cnf_transformation,[],[f12])).
% 0.23/0.48  fof(f12,plain,(
% 0.23/0.48    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.23/0.48    inference(flattening,[],[f11])).
% 0.23/0.48  fof(f11,plain,(
% 0.23/0.48    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.23/0.48    inference(ennf_transformation,[],[f10])).
% 0.23/0.48  fof(f10,negated_conjecture,(
% 0.23/0.48    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.23/0.48    inference(negated_conjecture,[],[f9])).
% 0.23/0.48  fof(f9,conjecture,(
% 0.23/0.48    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).
% 0.23/0.48  fof(f78,plain,(
% 0.23/0.48    spl4_7),
% 0.23/0.48    inference(avatar_split_clause,[],[f26,f76])).
% 0.23/0.48  fof(f26,plain,(
% 0.23/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.48    inference(cnf_transformation,[],[f12])).
% 0.23/0.48  fof(f74,plain,(
% 0.23/0.48    spl4_6),
% 0.23/0.48    inference(avatar_split_clause,[],[f28,f72])).
% 0.23/0.48  fof(f28,plain,(
% 0.23/0.48    v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.23/0.48    inference(cnf_transformation,[],[f12])).
% 0.23/0.48  fof(f70,plain,(
% 0.23/0.48    spl4_5),
% 0.23/0.48    inference(avatar_split_clause,[],[f27,f68])).
% 0.23/0.48  fof(f27,plain,(
% 0.23/0.48    v3_tex_2(sK1,sK0)),
% 0.23/0.48    inference(cnf_transformation,[],[f12])).
% 0.23/0.48  fof(f66,plain,(
% 0.23/0.48    spl4_4),
% 0.23/0.48    inference(avatar_split_clause,[],[f32,f64])).
% 0.23/0.48  fof(f32,plain,(
% 0.23/0.48    l1_pre_topc(sK0)),
% 0.23/0.48    inference(cnf_transformation,[],[f12])).
% 0.23/0.48  fof(f62,plain,(
% 0.23/0.48    spl4_3),
% 0.23/0.48    inference(avatar_split_clause,[],[f31,f60])).
% 0.23/0.48  fof(f31,plain,(
% 0.23/0.48    v3_tdlat_3(sK0)),
% 0.23/0.48    inference(cnf_transformation,[],[f12])).
% 0.23/0.48  fof(f58,plain,(
% 0.23/0.48    spl4_2),
% 0.23/0.48    inference(avatar_split_clause,[],[f30,f56])).
% 0.23/0.48  fof(f30,plain,(
% 0.23/0.48    v2_pre_topc(sK0)),
% 0.23/0.48    inference(cnf_transformation,[],[f12])).
% 0.23/0.48  fof(f54,plain,(
% 0.23/0.48    ~spl4_1),
% 0.23/0.48    inference(avatar_split_clause,[],[f29,f52])).
% 0.23/0.48  fof(f29,plain,(
% 0.23/0.48    ~v2_struct_0(sK0)),
% 0.23/0.48    inference(cnf_transformation,[],[f12])).
% 0.23/0.48  % SZS output end Proof for theBenchmark
% 0.23/0.48  % (8962)------------------------------
% 0.23/0.48  % (8962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.48  % (8962)Termination reason: Refutation
% 0.23/0.48  
% 0.23/0.48  % (8962)Memory used [KB]: 10618
% 0.23/0.48  % (8962)Time elapsed: 0.064 s
% 0.23/0.48  % (8962)------------------------------
% 0.23/0.48  % (8962)------------------------------
% 0.23/0.49  % (8952)Success in time 0.118 s
%------------------------------------------------------------------------------
