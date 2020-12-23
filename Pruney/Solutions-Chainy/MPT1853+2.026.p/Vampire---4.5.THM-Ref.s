%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 292 expanded)
%              Number of leaves         :   38 ( 128 expanded)
%              Depth                    :    8
%              Number of atoms          :  661 (1057 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f64,f68,f75,f78,f82,f86,f94,f98,f102,f110,f114,f118,f126,f133,f139,f143,f148,f155,f175,f180,f183,f193,f200,f205,f236,f245,f248,f253])).

fof(f253,plain,
    ( ~ spl2_3
    | ~ spl2_5
    | ~ spl2_32 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_32 ),
    inference(subsumption_resolution,[],[f250,f74])).

fof(f74,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_5
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f250,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl2_3
    | ~ spl2_32 ),
    inference(resolution,[],[f235,f67])).

fof(f67,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) )
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f234])).

% (16837)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f234,plain,
    ( spl2_32
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f248,plain,
    ( ~ spl2_2
    | ~ spl2_7
    | ~ spl2_18
    | spl2_33 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_18
    | spl2_33 ),
    inference(unit_resulting_resolution,[],[f63,f132,f240,f85])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f240,plain,
    ( ~ l1_pre_topc(k1_tex_2(sK0,sK1))
    | spl2_33 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl2_33
  <=> l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f132,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl2_18
  <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f63,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f245,plain,
    ( ~ spl2_33
    | ~ spl2_6
    | spl2_31 ),
    inference(avatar_split_clause,[],[f237,f231,f80,f239])).

fof(f80,plain,
    ( spl2_6
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f231,plain,
    ( spl2_31
  <=> l1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f237,plain,
    ( ~ l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl2_6
    | spl2_31 ),
    inference(resolution,[],[f232,f81])).

fof(f81,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f232,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | spl2_31 ),
    inference(avatar_component_clause,[],[f231])).

fof(f236,plain,
    ( ~ spl2_31
    | spl2_32
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_23
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f223,f203,f153,f66,f62,f58,f234,f231])).

fof(f58,plain,
    ( spl2_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f153,plain,
    ( spl2_23
  <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f203,plain,
    ( spl2_27
  <=> ! [X1,X0,X2] :
        ( ~ l1_struct_0(k1_tex_2(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(k1_tex_2(X0,X1)))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(X0,X1)),X2),u1_struct_0(k1_tex_2(X0,X1)))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_struct_0(k1_tex_2(sK0,sK1))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) )
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_23
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f222,f59])).

fof(f59,plain,
    ( ~ v2_struct_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_struct_0(k1_tex_2(sK0,sK1))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_23
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f221,f67])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_struct_0(k1_tex_2(sK0,sK1))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl2_2
    | ~ spl2_23
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f216,f63])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_struct_0(k1_tex_2(sK0,sK1))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl2_23
    | ~ spl2_27 ),
    inference(superposition,[],[f204,f154])).

fof(f154,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f153])).

fof(f204,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(k1_tex_2(X0,X1)))
        | ~ l1_struct_0(k1_tex_2(X0,X1))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(X0,X1)),X2),u1_struct_0(k1_tex_2(X0,X1)))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f203])).

% (16840)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f205,plain,
    ( spl2_27
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f157,f146,f108,f100,f203])).

fof(f100,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f108,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v7_struct_0(k1_tex_2(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f146,plain,
    ( spl2_21
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
        | ~ v7_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f157,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_struct_0(k1_tex_2(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(k1_tex_2(X0,X1)))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(X0,X1)),X2),u1_struct_0(k1_tex_2(X0,X1)))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_21 ),
    inference(subsumption_resolution,[],[f156,f101])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ v2_struct_0(k1_tex_2(X0,X1))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f100])).

% (16847)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f156,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_struct_0(k1_tex_2(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(k1_tex_2(X0,X1)))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(X0,X1)),X2),u1_struct_0(k1_tex_2(X0,X1)))
        | v2_struct_0(k1_tex_2(X0,X1))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl2_13
    | ~ spl2_21 ),
    inference(resolution,[],[f147,f109])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( v7_struct_0(k1_tex_2(X0,X1))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f108])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( ~ v7_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f146])).

fof(f200,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_26 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f198,f59])).

fof(f198,plain,
    ( v2_struct_0(sK0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f197,f67])).

fof(f197,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl2_2
    | ~ spl2_11
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f195,f63])).

fof(f195,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl2_11
    | ~ spl2_26 ),
    inference(resolution,[],[f192,f101])).

fof(f192,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl2_26
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f193,plain,
    ( spl2_26
    | spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f189,f173,f131,f124,f70,f62,f58,f191])).

fof(f70,plain,
    ( spl2_4
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f124,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v7_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ v1_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f173,plain,
    ( spl2_25
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f189,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_25 ),
    inference(subsumption_resolution,[],[f188,f59])).

fof(f188,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_25 ),
    inference(subsumption_resolution,[],[f187,f132])).

fof(f187,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_25 ),
    inference(subsumption_resolution,[],[f186,f63])).

fof(f186,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_17
    | ~ spl2_25 ),
    inference(subsumption_resolution,[],[f184,f174])).

fof(f174,plain,
    ( v7_struct_0(sK0)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f173])).

fof(f184,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_17 ),
    inference(resolution,[],[f71,f125])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( ~ v1_tex_2(X1,X0)
        | ~ v7_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | v2_struct_0(X0) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f124])).

fof(f71,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f183,plain,
    ( spl2_4
    | ~ spl2_2
    | ~ spl2_15
    | ~ spl2_18
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f165,f150,f131,f116,f62,f70])).

fof(f116,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v1_tex_2(X1,X0)
        | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f150,plain,
    ( spl2_22
  <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f165,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl2_2
    | ~ spl2_15
    | ~ spl2_18
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f161,f63])).

fof(f161,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_15
    | ~ spl2_18
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f159,f132])).

fof(f159,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_15
    | ~ spl2_22 ),
    inference(resolution,[],[f151,f117])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_pre_topc(X1,X0)
        | v1_tex_2(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f116])).

fof(f151,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f150])).

fof(f180,plain,
    ( ~ spl2_2
    | ~ spl2_6
    | spl2_24 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_6
    | spl2_24 ),
    inference(subsumption_resolution,[],[f177,f63])).

fof(f177,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_6
    | spl2_24 ),
    inference(resolution,[],[f171,f81])).

fof(f171,plain,
    ( ~ l1_struct_0(sK0)
    | spl2_24 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl2_24
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f175,plain,
    ( ~ spl2_24
    | spl2_25
    | spl2_1
    | ~ spl2_3
    | spl2_5
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f168,f141,f73,f66,f58,f173,f170])).

fof(f141,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | v7_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f168,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | spl2_1
    | ~ spl2_3
    | spl2_5
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f167,f59])).

fof(f167,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_3
    | spl2_5
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f166,f67])).

fof(f166,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl2_5
    | ~ spl2_20 ),
    inference(resolution,[],[f77,f142])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
        | v7_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f141])).

fof(f77,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f155,plain,
    ( spl2_22
    | spl2_23
    | ~ spl2_9
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f144,f137,f92,f153,f150])).

fof(f92,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | X0 = X1
        | v1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f137,plain,
    ( spl2_19
  <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f144,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl2_9
    | ~ spl2_19 ),
    inference(resolution,[],[f138,f93])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | X0 = X1
        | v1_subset_1(X1,X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f138,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f137])).

fof(f148,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f42,f146])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

fof(f143,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f41,f141])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

% (16847)Refutation not found, incomplete strategy% (16847)------------------------------
% (16847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16847)Termination reason: Refutation not found, incomplete strategy

% (16847)Memory used [KB]: 1663
% (16847)Time elapsed: 0.085 s
% (16847)------------------------------
% (16847)------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).

fof(f139,plain,
    ( spl2_19
    | ~ spl2_2
    | ~ spl2_10
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f135,f131,f96,f62,f137])).

fof(f96,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f135,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_10
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f134,f63])).

fof(f134,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_10
    | ~ spl2_18 ),
    inference(resolution,[],[f132,f97])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f133,plain,
    ( spl2_18
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f129,f112,f66,f62,f58,f131])).

fof(f112,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f129,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f128,f59])).

fof(f128,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f127,f63])).

fof(f127,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(resolution,[],[f113,f67])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | m1_pre_topc(k1_tex_2(X0,X1),X0) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f112])).

fof(f126,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f43,f124])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v7_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).

fof(f118,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f55,f116])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_tex_2(X1,X0)
      | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f52,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0)
      | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v1_tex_2(X1,X0)
      | ~ v1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v1_subset_1(X2,u1_struct_0(X0))
                <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tex_2)).

fof(f114,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f48,f112])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f110,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f50,f108])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v7_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f102,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f46,f100])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f98,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f38,f96])).

fof(f94,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f44,f92])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f86,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f37,f84])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f82,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f36,f80])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f78,plain,
    ( ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f32,f73,f70])).

fof(f32,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

fof(f75,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f31,f73,f70])).

fof(f31,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f33,f66])).

fof(f33,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f35,f62])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f34,f58])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (16844)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (16838)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (16844)Refutation not found, incomplete strategy% (16844)------------------------------
% 0.21/0.49  % (16844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (16844)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (16844)Memory used [KB]: 6140
% 0.21/0.49  % (16844)Time elapsed: 0.071 s
% 0.21/0.49  % (16844)------------------------------
% 0.21/0.49  % (16844)------------------------------
% 0.21/0.49  % (16848)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (16854)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (16833)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (16835)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (16854)Refutation not found, incomplete strategy% (16854)------------------------------
% 0.21/0.50  % (16854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16854)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (16854)Memory used [KB]: 10490
% 0.21/0.50  % (16854)Time elapsed: 0.071 s
% 0.21/0.50  % (16854)------------------------------
% 0.21/0.50  % (16854)------------------------------
% 0.21/0.50  % (16833)Refutation not found, incomplete strategy% (16833)------------------------------
% 0.21/0.50  % (16833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16833)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (16833)Memory used [KB]: 10618
% 0.21/0.50  % (16833)Time elapsed: 0.073 s
% 0.21/0.50  % (16833)------------------------------
% 0.21/0.50  % (16833)------------------------------
% 0.21/0.50  % (16842)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (16843)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (16843)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f254,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f60,f64,f68,f75,f78,f82,f86,f94,f98,f102,f110,f114,f118,f126,f133,f139,f143,f148,f155,f175,f180,f183,f193,f200,f205,f236,f245,f248,f253])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    ~spl2_3 | ~spl2_5 | ~spl2_32),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f252])).
% 0.21/0.51  fof(f252,plain,(
% 0.21/0.51    $false | (~spl2_3 | ~spl2_5 | ~spl2_32)),
% 0.21/0.51    inference(subsumption_resolution,[],[f250,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl2_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    spl2_5 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.51  fof(f250,plain,(
% 0.21/0.51    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl2_3 | ~spl2_32)),
% 0.21/0.51    inference(resolution,[],[f235,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl2_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    spl2_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))) ) | ~spl2_32),
% 0.21/0.51    inference(avatar_component_clause,[],[f234])).
% 0.21/0.51  % (16837)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    spl2_32 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.51  fof(f248,plain,(
% 0.21/0.51    ~spl2_2 | ~spl2_7 | ~spl2_18 | spl2_33),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f246])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    $false | (~spl2_2 | ~spl2_7 | ~spl2_18 | spl2_33)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f63,f132,f240,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl2_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl2_7 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    ~l1_pre_topc(k1_tex_2(sK0,sK1)) | spl2_33),
% 0.21/0.51    inference(avatar_component_clause,[],[f239])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    spl2_33 <=> l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl2_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f131])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    spl2_18 <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl2_2 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    ~spl2_33 | ~spl2_6 | spl2_31),
% 0.21/0.51    inference(avatar_split_clause,[],[f237,f231,f80,f239])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl2_6 <=> ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.51  fof(f231,plain,(
% 0.21/0.51    spl2_31 <=> l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    ~l1_pre_topc(k1_tex_2(sK0,sK1)) | (~spl2_6 | spl2_31)),
% 0.21/0.51    inference(resolution,[],[f232,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl2_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f80])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    ~l1_struct_0(k1_tex_2(sK0,sK1)) | spl2_31),
% 0.21/0.51    inference(avatar_component_clause,[],[f231])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    ~spl2_31 | spl2_32 | spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_23 | ~spl2_27),
% 0.21/0.51    inference(avatar_split_clause,[],[f223,f203,f153,f66,f62,f58,f234,f231])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    spl2_1 <=> v2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    spl2_23 <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    spl2_27 <=> ! [X1,X0,X2] : (~l1_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(k1_tex_2(X0,X1))) | ~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(X0,X1)),X2),u1_struct_0(k1_tex_2(X0,X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))) ) | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_23 | ~spl2_27)),
% 0.21/0.51    inference(subsumption_resolution,[],[f222,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ~v2_struct_0(sK0) | spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f58])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl2_2 | ~spl2_3 | ~spl2_23 | ~spl2_27)),
% 0.21/0.51    inference(subsumption_resolution,[],[f221,f67])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl2_2 | ~spl2_23 | ~spl2_27)),
% 0.21/0.51    inference(subsumption_resolution,[],[f216,f63])).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl2_23 | ~spl2_27)),
% 0.21/0.51    inference(superposition,[],[f204,f154])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~spl2_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f153])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k1_tex_2(X0,X1))) | ~l1_struct_0(k1_tex_2(X0,X1)) | ~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(X0,X1)),X2),u1_struct_0(k1_tex_2(X0,X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl2_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f203])).
% 0.21/0.51  % (16840)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    spl2_27 | ~spl2_11 | ~spl2_13 | ~spl2_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f157,f146,f108,f100,f203])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl2_11 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_struct_0(k1_tex_2(X0,X1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    spl2_13 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v7_struct_0(k1_tex_2(X0,X1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    spl2_21 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v7_struct_0(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(k1_tex_2(X0,X1))) | ~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(X0,X1)),X2),u1_struct_0(k1_tex_2(X0,X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | (~spl2_11 | ~spl2_13 | ~spl2_21)),
% 0.21/0.51    inference(subsumption_resolution,[],[f156,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl2_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f100])).
% 0.21/0.51  % (16847)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(k1_tex_2(X0,X1))) | ~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(X0,X1)),X2),u1_struct_0(k1_tex_2(X0,X1))) | v2_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | (~spl2_13 | ~spl2_21)),
% 0.21/0.51    inference(resolution,[],[f147,f109])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl2_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f108])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl2_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f146])).
% 0.21/0.51  fof(f200,plain,(
% 0.21/0.51    spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_11 | ~spl2_26),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f199])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    $false | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_11 | ~spl2_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f198,f59])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    v2_struct_0(sK0) | (~spl2_2 | ~spl2_3 | ~spl2_11 | ~spl2_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f197,f67])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl2_2 | ~spl2_11 | ~spl2_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f195,f63])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl2_11 | ~spl2_26)),
% 0.21/0.51    inference(resolution,[],[f192,f101])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl2_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f191])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    spl2_26 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    spl2_26 | spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_17 | ~spl2_18 | ~spl2_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f189,f173,f131,f124,f70,f62,f58,f191])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl2_4 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    spl2_17 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v7_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~v1_tex_2(X1,X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    spl2_25 <=> v7_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    v2_struct_0(k1_tex_2(sK0,sK1)) | (spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_17 | ~spl2_18 | ~spl2_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f188,f59])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | (~spl2_2 | ~spl2_4 | ~spl2_17 | ~spl2_18 | ~spl2_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f187,f132])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | (~spl2_2 | ~spl2_4 | ~spl2_17 | ~spl2_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f186,f63])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | (~spl2_4 | ~spl2_17 | ~spl2_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f184,f174])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    v7_struct_0(sK0) | ~spl2_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f173])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    ~v7_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | (~spl2_4 | ~spl2_17)),
% 0.21/0.51    inference(resolution,[],[f71,f125])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | ~v7_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | v2_struct_0(X0)) ) | ~spl2_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f124])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl2_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f70])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    spl2_4 | ~spl2_2 | ~spl2_15 | ~spl2_18 | ~spl2_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f165,f150,f131,f116,f62,f70])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl2_15 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_tex_2(X1,X0) | ~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    spl2_22 <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl2_2 | ~spl2_15 | ~spl2_18 | ~spl2_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f161,f63])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | (~spl2_15 | ~spl2_18 | ~spl2_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f159,f132])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | (~spl2_15 | ~spl2_22)),
% 0.21/0.51    inference(resolution,[],[f151,f117])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v1_tex_2(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl2_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f116])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~spl2_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f150])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    ~spl2_2 | ~spl2_6 | spl2_24),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f179])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    $false | (~spl2_2 | ~spl2_6 | spl2_24)),
% 0.21/0.51    inference(subsumption_resolution,[],[f177,f63])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | (~spl2_6 | spl2_24)),
% 0.21/0.51    inference(resolution,[],[f171,f81])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    ~l1_struct_0(sK0) | spl2_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f170])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    spl2_24 <=> l1_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    ~spl2_24 | spl2_25 | spl2_1 | ~spl2_3 | spl2_5 | ~spl2_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f168,f141,f73,f66,f58,f173,f170])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    spl2_20 <=> ! [X1,X0] : (v2_struct_0(X0) | v7_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    v7_struct_0(sK0) | ~l1_struct_0(sK0) | (spl2_1 | ~spl2_3 | spl2_5 | ~spl2_20)),
% 0.21/0.51    inference(subsumption_resolution,[],[f167,f59])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    v7_struct_0(sK0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl2_3 | spl2_5 | ~spl2_20)),
% 0.21/0.51    inference(subsumption_resolution,[],[f166,f67])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    v7_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (spl2_5 | ~spl2_20)),
% 0.21/0.51    inference(resolution,[],[f77,f142])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v7_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl2_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f141])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl2_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f73])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    spl2_22 | spl2_23 | ~spl2_9 | ~spl2_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f144,f137,f92,f153,f150])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl2_9 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    spl2_19 <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | (~spl2_9 | ~spl2_19)),
% 0.21/0.51    inference(resolution,[],[f138,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) ) | ~spl2_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f92])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f137])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    spl2_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f42,f146])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v7_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    spl2_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f41,f141])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | v7_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  % (16847)Refutation not found, incomplete strategy% (16847)------------------------------
% 0.21/0.51  % (16847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16847)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16847)Memory used [KB]: 1663
% 0.21/0.51  % (16847)Time elapsed: 0.085 s
% 0.21/0.51  % (16847)------------------------------
% 0.21/0.51  % (16847)------------------------------
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    spl2_19 | ~spl2_2 | ~spl2_10 | ~spl2_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f135,f131,f96,f62,f137])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl2_10 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_10 | ~spl2_18)),
% 0.21/0.51    inference(subsumption_resolution,[],[f134,f63])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_10 | ~spl2_18)),
% 0.21/0.51    inference(resolution,[],[f132,f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl2_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f96])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    spl2_18 | spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f129,f112,f66,f62,f58,f131])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    spl2_14 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f128,f59])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | (~spl2_2 | ~spl2_3 | ~spl2_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f127,f63])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | (~spl2_3 | ~spl2_14)),
% 0.21/0.51    inference(resolution,[],[f113,f67])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_pre_topc(k1_tex_2(X0,X1),X0)) ) | ~spl2_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f112])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    spl2_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f43,f124])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~v7_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~v1_tex_2(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    spl2_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f55,f116])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_tex_2(X1,X0) | ~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f52,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0) | ~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.21/0.51    inference(equality_resolution,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tex_2)).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl2_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f112])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl2_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f50,f108])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v7_struct_0(k1_tex_2(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    spl2_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f46,f100])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_struct_0(k1_tex_2(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    spl2_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f38,f96])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl2_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f44,f92])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl2_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f84])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl2_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f80])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~spl2_4 | ~spl2_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f73,f70])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f11])).
% 0.21/0.51  fof(f11,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl2_4 | spl2_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f31,f73,f70])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f66])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f62])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ~spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f58])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (16843)------------------------------
% 0.21/0.51  % (16843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16843)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (16843)Memory used [KB]: 10746
% 0.21/0.51  % (16843)Time elapsed: 0.076 s
% 0.21/0.51  % (16843)------------------------------
% 0.21/0.51  % (16843)------------------------------
% 0.21/0.51  % (16839)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (16831)Success in time 0.153 s
%------------------------------------------------------------------------------
