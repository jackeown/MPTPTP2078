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
% DateTime   : Thu Dec  3 13:21:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 273 expanded)
%              Number of leaves         :   40 ( 127 expanded)
%              Depth                    :    7
%              Number of atoms          :  539 ( 907 expanded)
%              Number of equality atoms :   60 (  97 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (26793)Refutation not found, incomplete strategy% (26793)------------------------------
% (26793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26793)Termination reason: Refutation not found, incomplete strategy

% (26793)Memory used [KB]: 6140
% (26793)Time elapsed: 0.093 s
% (26793)------------------------------
% (26793)------------------------------
% (26804)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (26809)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% (26804)Refutation not found, incomplete strategy% (26804)------------------------------
% (26804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26804)Termination reason: Refutation not found, incomplete strategy

% (26804)Memory used [KB]: 10618
% (26804)Time elapsed: 0.099 s
% (26804)------------------------------
% (26804)------------------------------
% (26810)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (26801)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (26812)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (26803)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f275,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f62,f66,f70,f78,f82,f86,f94,f99,f107,f111,f120,f124,f128,f133,f137,f147,f151,f155,f162,f189,f193,f203,f210,f217,f231,f235,f240,f263,f274])).

fof(f274,plain,
    ( ~ spl5_7
    | ~ spl5_30
    | ~ spl5_37
    | ~ spl5_41 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | ~ spl5_7
    | ~ spl5_30
    | ~ spl5_37
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f272,f192])).

fof(f192,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl5_30
  <=> v3_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f272,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl5_7
    | ~ spl5_37
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f270,f77])).

fof(f77,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_7
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f270,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl5_37
    | ~ spl5_41 ),
    inference(trivial_inequality_removal,[],[f269])).

fof(f269,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl5_37
    | ~ spl5_41 ),
    inference(superposition,[],[f262,f234])).

fof(f234,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl5_37
  <=> ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f262,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl5_41
  <=> ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f263,plain,
    ( spl5_41
    | ~ spl5_4
    | ~ spl5_7
    | spl5_11
    | ~ spl5_36
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f246,f238,f229,f97,f76,f64,f261])).

fof(f64,plain,
    ( spl5_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f97,plain,
    ( spl5_11
  <=> v2_tex_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f229,plain,
    ( spl5_36
  <=> ! [X1,X0,X2] :
        ( k3_xboole_0(X1,X2) != sK2(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X2,X0)
        | ~ l1_pre_topc(X0)
        | v2_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f238,plain,
    ( spl5_38
  <=> k1_xboole_0 = sK2(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f246,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl5_4
    | ~ spl5_7
    | spl5_11
    | ~ spl5_36
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f245,f98])).

fof(f98,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK0)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f245,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v2_tex_2(k1_xboole_0,sK0) )
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_36
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f244,f65])).

fof(f65,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f244,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_tex_2(k1_xboole_0,sK0) )
    | ~ spl5_7
    | ~ spl5_36
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f242,f77])).

fof(f242,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_tex_2(k1_xboole_0,sK0) )
    | ~ spl5_36
    | ~ spl5_38 ),
    inference(superposition,[],[f230,f239])).

fof(f239,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f238])).

fof(f230,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(X1,X2) != sK2(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X2,X0)
        | ~ l1_pre_topc(X0)
        | v2_tex_2(X1,X0) )
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f229])).

fof(f240,plain,
    ( spl5_38
    | ~ spl5_7
    | ~ spl5_9
    | spl5_11
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f213,f208,f97,f84,f76,f238])).

fof(f84,plain,
    ( spl5_9
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f208,plain,
    ( spl5_33
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK2(sK0,X0),X0)
        | v2_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f213,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl5_7
    | ~ spl5_9
    | spl5_11
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f212,f98])).

fof(f212,plain,
    ( v2_tex_2(k1_xboole_0,sK0)
    | k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f211,f77])).

fof(f211,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(k1_xboole_0,sK0)
    | k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl5_9
    | ~ spl5_33 ),
    inference(resolution,[],[f209,f85])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f209,plain,
    ( ! [X0] :
        ( r1_tarski(sK2(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f208])).

fof(f235,plain,
    ( spl5_37
    | ~ spl5_7
    | ~ spl5_19
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f225,f215,f131,f76,f233])).

fof(f131,plain,
    ( spl5_19
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f215,plain,
    ( spl5_34
  <=> ! [X0] : k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f225,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)
    | ~ spl5_7
    | ~ spl5_19
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f222,f77])).

fof(f222,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl5_19
    | ~ spl5_34 ),
    inference(superposition,[],[f216,f132])).

fof(f132,plain,
    ( ! [X2,X0,X1] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f131])).

fof(f216,plain,
    ( ! [X0] : k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,k1_xboole_0)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f215])).

fof(f231,plain,
    ( spl5_36
    | ~ spl5_19
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f199,f187,f131,f229])).

fof(f187,plain,
    ( spl5_29
  <=> ! [X1,X3,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X3,X0)
        | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
        | v2_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f199,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(X1,X2) != sK2(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X2,X0)
        | ~ l1_pre_topc(X0)
        | v2_tex_2(X1,X0) )
    | ~ spl5_19
    | ~ spl5_29 ),
    inference(duplicate_literal_removal,[],[f198])).

fof(f198,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(X1,X2) != sK2(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X2,X0)
        | ~ l1_pre_topc(X0)
        | v2_tex_2(X1,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl5_19
    | ~ spl5_29 ),
    inference(superposition,[],[f188,f132])).

fof(f188,plain,
    ( ! [X0,X3,X1] :
        ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X3,X0)
        | ~ l1_pre_topc(X0)
        | v2_tex_2(X1,X0) )
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f187])).

fof(f217,plain,
    ( spl5_34
    | ~ spl5_7
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f204,f201,f76,f215])).

fof(f201,plain,
    ( spl5_32
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f204,plain,
    ( ! [X0] : k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,k1_xboole_0)
    | ~ spl5_7
    | ~ spl5_32 ),
    inference(resolution,[],[f202,f77])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,X1) )
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f201])).

fof(f210,plain,
    ( spl5_33
    | ~ spl5_4
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f158,f153,f64,f208])).

fof(f153,plain,
    ( spl5_23
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(sK2(X0,X1),X1)
        | v2_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK2(sK0,X0),X0)
        | v2_tex_2(X0,sK0) )
    | ~ spl5_4
    | ~ spl5_23 ),
    inference(resolution,[],[f154,f65])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(sK2(X0,X1),X1)
        | v2_tex_2(X1,X0) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f153])).

fof(f203,plain,
    ( spl5_32
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f140,f135,f118,f201])).

fof(f118,plain,
    ( spl5_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f135,plain,
    ( spl5_20
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(resolution,[],[f136,f119])).

fof(f119,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f118])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f135])).

fof(f193,plain,
    ( spl5_30
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_21
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f172,f160,f145,f76,f64,f60,f191])).

fof(f60,plain,
    ( spl5_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f145,plain,
    ( spl5_21
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f160,plain,
    ( spl5_24
  <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f172,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_21
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f171,f61])).

fof(f61,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f171,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_21
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f170,f77])).

fof(f170,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_21
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f168,f65])).

fof(f168,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_21
    | ~ spl5_24 ),
    inference(superposition,[],[f146,f161])).

fof(f161,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f160])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(k1_tops_1(X0,X1),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f145])).

fof(f189,plain,(
    spl5_29 ),
    inference(avatar_split_clause,[],[f38,f187])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

fof(f162,plain,
    ( spl5_24
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f157,f149,f84,f76,f160])).

fof(f149,plain,
    ( spl5_22
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f157,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f156,f77])).

fof(f156,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl5_9
    | ~ spl5_22 ),
    inference(resolution,[],[f150,f85])).

fof(f150,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f149])).

fof(f155,plain,(
    spl5_23 ),
    inference(avatar_split_clause,[],[f43,f153])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f151,plain,
    ( spl5_22
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f138,f126,f64,f149])).

fof(f126,plain,
    ( spl5_18
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) )
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(resolution,[],[f127,f65])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(k1_tops_1(X0,X1),X1) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f126])).

fof(f147,plain,(
    spl5_21 ),
    inference(avatar_split_clause,[],[f46,f145])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f137,plain,
    ( spl5_20
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f129,f122,f105,f135])).

fof(f105,plain,
    ( spl5_13
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK4(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f122,plain,
    ( spl5_17
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(resolution,[],[f123,f106])).

fof(f106,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f105])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f122])).

fof(f133,plain,(
    spl5_19 ),
    inference(avatar_split_clause,[],[f48,f131])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f128,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f37,f126])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f124,plain,
    ( spl5_17
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f116,f109,f92,f122])).

fof(f92,plain,
    ( spl5_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f109,plain,
    ( spl5_14
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(resolution,[],[f110,f93])).

fof(f93,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f92])).

fof(f110,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f109])).

fof(f120,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f47,f118])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f111,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f50,f109])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f107,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f45,f105])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f99,plain,
    ( ~ spl5_11
    | ~ spl5_1
    | spl5_5
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f89,f80,f68,f52,f97])).

fof(f52,plain,
    ( spl5_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f68,plain,
    ( spl5_5
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f80,plain,
    ( spl5_8
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f89,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK0)
    | ~ spl5_1
    | spl5_5
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f69,f87])).

fof(f87,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(resolution,[],[f81,f53])).

fof(f53,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f69,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f94,plain,
    ( spl5_10
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f90,f80,f52,f92])).

fof(f90,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f53,f87])).

fof(f86,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f44,f84])).

fof(f44,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f82,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f36,f80])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f78,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f35,f76])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f70,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f31,f68])).

fof(f31,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f66,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f34,f64])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f33,f60])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f29,f52])).

fof(f29,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:03:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.47  % (26798)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (26807)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (26800)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (26796)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (26797)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (26813)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (26813)Refutation not found, incomplete strategy% (26813)------------------------------
% 0.20/0.48  % (26813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (26813)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (26813)Memory used [KB]: 10618
% 0.20/0.48  % (26813)Time elapsed: 0.071 s
% 0.20/0.48  % (26813)------------------------------
% 0.20/0.48  % (26813)------------------------------
% 0.20/0.49  % (26806)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (26805)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (26794)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (26794)Refutation not found, incomplete strategy% (26794)------------------------------
% 0.20/0.50  % (26794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (26794)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (26794)Memory used [KB]: 10618
% 0.20/0.50  % (26794)Time elapsed: 0.082 s
% 0.20/0.50  % (26794)------------------------------
% 0.20/0.50  % (26794)------------------------------
% 0.20/0.50  % (26795)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (26799)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (26811)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (26802)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (26808)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (26793)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (26802)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  % (26793)Refutation not found, incomplete strategy% (26793)------------------------------
% 0.20/0.50  % (26793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (26793)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (26793)Memory used [KB]: 6140
% 0.20/0.50  % (26793)Time elapsed: 0.093 s
% 0.20/0.50  % (26793)------------------------------
% 0.20/0.50  % (26793)------------------------------
% 0.20/0.51  % (26804)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (26809)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (26804)Refutation not found, incomplete strategy% (26804)------------------------------
% 0.20/0.51  % (26804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26804)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26804)Memory used [KB]: 10618
% 0.20/0.51  % (26804)Time elapsed: 0.099 s
% 0.20/0.51  % (26804)------------------------------
% 0.20/0.51  % (26804)------------------------------
% 0.20/0.51  % (26810)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (26801)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.51  % (26812)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (26803)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.53  fof(f275,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f54,f62,f66,f70,f78,f82,f86,f94,f99,f107,f111,f120,f124,f128,f133,f137,f147,f151,f155,f162,f189,f193,f203,f210,f217,f231,f235,f240,f263,f274])).
% 0.20/0.53  fof(f274,plain,(
% 0.20/0.53    ~spl5_7 | ~spl5_30 | ~spl5_37 | ~spl5_41),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f273])).
% 0.20/0.53  fof(f273,plain,(
% 0.20/0.53    $false | (~spl5_7 | ~spl5_30 | ~spl5_37 | ~spl5_41)),
% 0.20/0.53    inference(subsumption_resolution,[],[f272,f192])).
% 0.20/0.53  fof(f192,plain,(
% 0.20/0.53    v3_pre_topc(k1_xboole_0,sK0) | ~spl5_30),
% 0.20/0.53    inference(avatar_component_clause,[],[f191])).
% 0.20/0.53  fof(f191,plain,(
% 0.20/0.53    spl5_30 <=> v3_pre_topc(k1_xboole_0,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.20/0.53  fof(f272,plain,(
% 0.20/0.53    ~v3_pre_topc(k1_xboole_0,sK0) | (~spl5_7 | ~spl5_37 | ~spl5_41)),
% 0.20/0.53    inference(subsumption_resolution,[],[f270,f77])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl5_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f76])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    spl5_7 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.53  fof(f270,plain,(
% 0.20/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k1_xboole_0,sK0) | (~spl5_37 | ~spl5_41)),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f269])).
% 0.20/0.53  fof(f269,plain,(
% 0.20/0.53    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k1_xboole_0,sK0) | (~spl5_37 | ~spl5_41)),
% 0.20/0.53    inference(superposition,[],[f262,f234])).
% 0.20/0.53  fof(f234,plain,(
% 0.20/0.53    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) ) | ~spl5_37),
% 0.20/0.53    inference(avatar_component_clause,[],[f233])).
% 0.20/0.53  fof(f233,plain,(
% 0.20/0.53    spl5_37 <=> ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0)) ) | ~spl5_41),
% 0.20/0.53    inference(avatar_component_clause,[],[f261])).
% 0.20/0.53  fof(f261,plain,(
% 0.20/0.53    spl5_41 <=> ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 0.20/0.53  fof(f263,plain,(
% 0.20/0.53    spl5_41 | ~spl5_4 | ~spl5_7 | spl5_11 | ~spl5_36 | ~spl5_38),
% 0.20/0.53    inference(avatar_split_clause,[],[f246,f238,f229,f97,f76,f64,f261])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    spl5_4 <=> l1_pre_topc(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    spl5_11 <=> v2_tex_2(k1_xboole_0,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    spl5_36 <=> ! [X1,X0,X2] : (k3_xboole_0(X1,X2) != sK2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.20/0.53  fof(f238,plain,(
% 0.20/0.53    spl5_38 <=> k1_xboole_0 = sK2(sK0,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 0.20/0.53  fof(f246,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0)) ) | (~spl5_4 | ~spl5_7 | spl5_11 | ~spl5_36 | ~spl5_38)),
% 0.20/0.53    inference(subsumption_resolution,[],[f245,f98])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    ~v2_tex_2(k1_xboole_0,sK0) | spl5_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f97])).
% 0.20/0.53  fof(f245,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | v2_tex_2(k1_xboole_0,sK0)) ) | (~spl5_4 | ~spl5_7 | ~spl5_36 | ~spl5_38)),
% 0.20/0.53    inference(subsumption_resolution,[],[f244,f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    l1_pre_topc(sK0) | ~spl5_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f64])).
% 0.20/0.53  fof(f244,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v2_tex_2(k1_xboole_0,sK0)) ) | (~spl5_7 | ~spl5_36 | ~spl5_38)),
% 0.20/0.53    inference(subsumption_resolution,[],[f242,f77])).
% 0.20/0.53  fof(f242,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v2_tex_2(k1_xboole_0,sK0)) ) | (~spl5_36 | ~spl5_38)),
% 0.20/0.53    inference(superposition,[],[f230,f239])).
% 0.20/0.53  fof(f239,plain,(
% 0.20/0.53    k1_xboole_0 = sK2(sK0,k1_xboole_0) | ~spl5_38),
% 0.20/0.53    inference(avatar_component_clause,[],[f238])).
% 0.20/0.53  fof(f230,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) != sK2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0)) ) | ~spl5_36),
% 0.20/0.53    inference(avatar_component_clause,[],[f229])).
% 0.20/0.53  fof(f240,plain,(
% 0.20/0.53    spl5_38 | ~spl5_7 | ~spl5_9 | spl5_11 | ~spl5_33),
% 0.20/0.53    inference(avatar_split_clause,[],[f213,f208,f97,f84,f76,f238])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    spl5_9 <=> ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.53  fof(f208,plain,(
% 0.20/0.53    spl5_33 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2(sK0,X0),X0) | v2_tex_2(X0,sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.20/0.53  fof(f213,plain,(
% 0.20/0.53    k1_xboole_0 = sK2(sK0,k1_xboole_0) | (~spl5_7 | ~spl5_9 | spl5_11 | ~spl5_33)),
% 0.20/0.53    inference(subsumption_resolution,[],[f212,f98])).
% 0.20/0.53  fof(f212,plain,(
% 0.20/0.53    v2_tex_2(k1_xboole_0,sK0) | k1_xboole_0 = sK2(sK0,k1_xboole_0) | (~spl5_7 | ~spl5_9 | ~spl5_33)),
% 0.20/0.53    inference(subsumption_resolution,[],[f211,f77])).
% 0.20/0.53  fof(f211,plain,(
% 0.20/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(k1_xboole_0,sK0) | k1_xboole_0 = sK2(sK0,k1_xboole_0) | (~spl5_9 | ~spl5_33)),
% 0.20/0.53    inference(resolution,[],[f209,f85])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl5_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f84])).
% 0.20/0.53  fof(f209,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(sK2(sK0,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | ~spl5_33),
% 0.20/0.53    inference(avatar_component_clause,[],[f208])).
% 0.20/0.53  fof(f235,plain,(
% 0.20/0.53    spl5_37 | ~spl5_7 | ~spl5_19 | ~spl5_34),
% 0.20/0.53    inference(avatar_split_clause,[],[f225,f215,f131,f76,f233])).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    spl5_19 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.53  fof(f215,plain,(
% 0.20/0.53    spl5_34 <=> ! [X0] : k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.20/0.53  fof(f225,plain,(
% 0.20/0.53    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) ) | (~spl5_7 | ~spl5_19 | ~spl5_34)),
% 0.20/0.53    inference(subsumption_resolution,[],[f222,f77])).
% 0.20/0.53  fof(f222,plain,(
% 0.20/0.53    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))) ) | (~spl5_19 | ~spl5_34)),
% 0.20/0.53    inference(superposition,[],[f216,f132])).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl5_19),
% 0.20/0.53    inference(avatar_component_clause,[],[f131])).
% 0.20/0.53  fof(f216,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,k1_xboole_0)) ) | ~spl5_34),
% 0.20/0.53    inference(avatar_component_clause,[],[f215])).
% 0.20/0.53  fof(f231,plain,(
% 0.20/0.53    spl5_36 | ~spl5_19 | ~spl5_29),
% 0.20/0.53    inference(avatar_split_clause,[],[f199,f187,f131,f229])).
% 0.20/0.53  fof(f187,plain,(
% 0.20/0.53    spl5_29 <=> ! [X1,X3,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | v2_tex_2(X1,X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.20/0.53  fof(f199,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) != sK2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0)) ) | (~spl5_19 | ~spl5_29)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f198])).
% 0.20/0.53  fof(f198,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) != sK2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) ) | (~spl5_19 | ~spl5_29)),
% 0.20/0.53    inference(superposition,[],[f188,f132])).
% 0.20/0.53  fof(f188,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0)) ) | ~spl5_29),
% 0.20/0.53    inference(avatar_component_clause,[],[f187])).
% 0.20/0.53  fof(f217,plain,(
% 0.20/0.53    spl5_34 | ~spl5_7 | ~spl5_32),
% 0.20/0.53    inference(avatar_split_clause,[],[f204,f201,f76,f215])).
% 0.20/0.53  fof(f201,plain,(
% 0.20/0.53    spl5_32 <=> ! [X1,X0] : (k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.20/0.53  fof(f204,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,k1_xboole_0)) ) | (~spl5_7 | ~spl5_32)),
% 0.20/0.53    inference(resolution,[],[f202,f77])).
% 0.20/0.53  fof(f202,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,X1)) ) | ~spl5_32),
% 0.20/0.53    inference(avatar_component_clause,[],[f201])).
% 0.20/0.53  fof(f210,plain,(
% 0.20/0.53    spl5_33 | ~spl5_4 | ~spl5_23),
% 0.20/0.53    inference(avatar_split_clause,[],[f158,f153,f64,f208])).
% 0.20/0.53  fof(f153,plain,(
% 0.20/0.53    spl5_23 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.20/0.53  fof(f158,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2(sK0,X0),X0) | v2_tex_2(X0,sK0)) ) | (~spl5_4 | ~spl5_23)),
% 0.20/0.53    inference(resolution,[],[f154,f65])).
% 0.20/0.53  fof(f154,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0)) ) | ~spl5_23),
% 0.20/0.53    inference(avatar_component_clause,[],[f153])).
% 0.20/0.53  fof(f203,plain,(
% 0.20/0.53    spl5_32 | ~spl5_16 | ~spl5_20),
% 0.20/0.53    inference(avatar_split_clause,[],[f140,f135,f118,f201])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    spl5_16 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    spl5_20 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) ) | (~spl5_16 | ~spl5_20)),
% 0.20/0.53    inference(resolution,[],[f136,f119])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl5_16),
% 0.20/0.53    inference(avatar_component_clause,[],[f118])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl5_20),
% 0.20/0.53    inference(avatar_component_clause,[],[f135])).
% 0.20/0.53  fof(f193,plain,(
% 0.20/0.53    spl5_30 | ~spl5_3 | ~spl5_4 | ~spl5_7 | ~spl5_21 | ~spl5_24),
% 0.20/0.53    inference(avatar_split_clause,[],[f172,f160,f145,f76,f64,f60,f191])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    spl5_3 <=> v2_pre_topc(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    spl5_21 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.20/0.53  fof(f160,plain,(
% 0.20/0.53    spl5_24 <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.20/0.53  fof(f172,plain,(
% 0.20/0.53    v3_pre_topc(k1_xboole_0,sK0) | (~spl5_3 | ~spl5_4 | ~spl5_7 | ~spl5_21 | ~spl5_24)),
% 0.20/0.53    inference(subsumption_resolution,[],[f171,f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    v2_pre_topc(sK0) | ~spl5_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f60])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    v3_pre_topc(k1_xboole_0,sK0) | ~v2_pre_topc(sK0) | (~spl5_4 | ~spl5_7 | ~spl5_21 | ~spl5_24)),
% 0.20/0.53    inference(subsumption_resolution,[],[f170,f77])).
% 0.20/0.53  fof(f170,plain,(
% 0.20/0.53    v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | (~spl5_4 | ~spl5_21 | ~spl5_24)),
% 0.20/0.53    inference(subsumption_resolution,[],[f168,f65])).
% 0.20/0.53  fof(f168,plain,(
% 0.20/0.53    v3_pre_topc(k1_xboole_0,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | (~spl5_21 | ~spl5_24)),
% 0.20/0.53    inference(superposition,[],[f146,f161])).
% 0.20/0.53  fof(f161,plain,(
% 0.20/0.53    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | ~spl5_24),
% 0.20/0.53    inference(avatar_component_clause,[],[f160])).
% 0.20/0.53  fof(f146,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) ) | ~spl5_21),
% 0.20/0.53    inference(avatar_component_clause,[],[f145])).
% 0.20/0.53  fof(f189,plain,(
% 0.20/0.53    spl5_29),
% 0.20/0.53    inference(avatar_split_clause,[],[f38,f187])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | v2_tex_2(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).
% 0.20/0.53  fof(f162,plain,(
% 0.20/0.53    spl5_24 | ~spl5_7 | ~spl5_9 | ~spl5_22),
% 0.20/0.53    inference(avatar_split_clause,[],[f157,f149,f84,f76,f160])).
% 0.20/0.53  fof(f149,plain,(
% 0.20/0.53    spl5_22 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.53  fof(f157,plain,(
% 0.20/0.53    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | (~spl5_7 | ~spl5_9 | ~spl5_22)),
% 0.20/0.53    inference(subsumption_resolution,[],[f156,f77])).
% 0.20/0.53  fof(f156,plain,(
% 0.20/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | (~spl5_9 | ~spl5_22)),
% 0.20/0.53    inference(resolution,[],[f150,f85])).
% 0.20/0.53  fof(f150,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_22),
% 0.20/0.53    inference(avatar_component_clause,[],[f149])).
% 0.20/0.53  fof(f155,plain,(
% 0.20/0.53    spl5_23),
% 0.20/0.53    inference(avatar_split_clause,[],[f43,f153])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f151,plain,(
% 0.20/0.53    spl5_22 | ~spl5_4 | ~spl5_18),
% 0.20/0.53    inference(avatar_split_clause,[],[f138,f126,f64,f149])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    spl5_18 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.53  fof(f138,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) ) | (~spl5_4 | ~spl5_18)),
% 0.20/0.53    inference(resolution,[],[f127,f65])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) ) | ~spl5_18),
% 0.20/0.53    inference(avatar_component_clause,[],[f126])).
% 0.20/0.53  fof(f147,plain,(
% 0.20/0.53    spl5_21),
% 0.20/0.53    inference(avatar_split_clause,[],[f46,f145])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.20/0.53  fof(f137,plain,(
% 0.20/0.53    spl5_20 | ~spl5_13 | ~spl5_17),
% 0.20/0.53    inference(avatar_split_clause,[],[f129,f122,f105,f135])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    spl5_13 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    spl5_17 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | (~spl5_13 | ~spl5_17)),
% 0.20/0.53    inference(resolution,[],[f123,f106])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) ) | ~spl5_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f105])).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl5_17),
% 0.20/0.53    inference(avatar_component_clause,[],[f122])).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    spl5_19),
% 0.20/0.53    inference(avatar_split_clause,[],[f48,f131])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    spl5_18),
% 0.20/0.53    inference(avatar_split_clause,[],[f37,f126])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    spl5_17 | ~spl5_10 | ~spl5_14),
% 0.20/0.53    inference(avatar_split_clause,[],[f116,f109,f92,f122])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    spl5_10 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    spl5_14 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | (~spl5_10 | ~spl5_14)),
% 0.20/0.53    inference(resolution,[],[f110,f93])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0) | ~spl5_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f92])).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) ) | ~spl5_14),
% 0.20/0.53    inference(avatar_component_clause,[],[f109])).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    spl5_16),
% 0.20/0.53    inference(avatar_split_clause,[],[f47,f118])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    spl5_14),
% 0.20/0.53    inference(avatar_split_clause,[],[f50,f109])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    spl5_13),
% 0.20/0.53    inference(avatar_split_clause,[],[f45,f105])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    ~spl5_11 | ~spl5_1 | spl5_5 | ~spl5_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f89,f80,f68,f52,f97])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    spl5_1 <=> v1_xboole_0(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    spl5_5 <=> v2_tex_2(sK1,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    spl5_8 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ~v2_tex_2(k1_xboole_0,sK0) | (~spl5_1 | spl5_5 | ~spl5_8)),
% 0.20/0.53    inference(backward_demodulation,[],[f69,f87])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | (~spl5_1 | ~spl5_8)),
% 0.20/0.53    inference(resolution,[],[f81,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    v1_xboole_0(sK1) | ~spl5_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f52])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl5_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f80])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ~v2_tex_2(sK1,sK0) | spl5_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f68])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    spl5_10 | ~spl5_1 | ~spl5_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f90,f80,f52,f92])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0) | (~spl5_1 | ~spl5_8)),
% 0.20/0.53    inference(backward_demodulation,[],[f53,f87])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    spl5_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f44,f84])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    spl5_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f36,f80])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    spl5_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f35,f76])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ~spl5_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f31,f68])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ~v2_tex_2(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.53    inference(negated_conjecture,[],[f12])).
% 0.20/0.53  fof(f12,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    spl5_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f34,f64])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    spl5_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f33,f60])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    v2_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    spl5_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f29,f52])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    v1_xboole_0(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (26802)------------------------------
% 0.20/0.53  % (26802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26802)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (26802)Memory used [KB]: 10746
% 0.20/0.53  % (26802)Time elapsed: 0.103 s
% 0.20/0.53  % (26802)------------------------------
% 0.20/0.53  % (26802)------------------------------
% 0.20/0.53  % (26791)Success in time 0.172 s
%------------------------------------------------------------------------------
