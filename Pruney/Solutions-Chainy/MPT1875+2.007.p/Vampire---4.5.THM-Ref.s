%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 258 expanded)
%              Number of leaves         :   39 ( 107 expanded)
%              Depth                    :    9
%              Number of atoms          :  596 ( 933 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f70,f74,f78,f82,f86,f90,f94,f106,f110,f122,f126,f138,f144,f152,f159,f163,f215,f229,f240,f250,f257,f271,f280,f289,f301,f312,f319])).

fof(f319,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_24
    | ~ spl4_48 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_24
    | ~ spl4_48 ),
    inference(unit_resulting_resolution,[],[f77,f65,f69,f81,f85,f300,f162])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0)
        | v2_tex_2(X1,X0) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl4_24
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r2_hidden(sK2(X0,X1),X1)
        | v2_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f300,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl4_48
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f85,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f81,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl4_5
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f69,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f65,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f77,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f312,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_39 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f310,f85])).

fof(f310,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_16
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f309,f65])).

fof(f309,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_16
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f308,f73])).

fof(f73,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_3
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f308,plain,
    ( ~ v1_tdlat_3(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_16
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f307,f77])).

fof(f307,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_16
    | ~ spl4_39 ),
    inference(duplicate_literal_removal,[],[f306])).

% (11607)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f306,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_16
    | ~ spl4_39 ),
    inference(resolution,[],[f249,f125])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f249,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_tdlat_3(X1)
        | v2_struct_0(X1) )
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl4_39
  <=> ! [X1] :
        ( ~ v1_tdlat_3(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f301,plain,
    ( spl4_48
    | ~ spl4_8
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f290,f278,f92,f299])).

fof(f92,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f278,plain,
    ( spl4_44
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f290,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl4_8
    | ~ spl4_44 ),
    inference(resolution,[],[f279,f93])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f279,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f278])).

fof(f289,plain,
    ( ~ spl4_30
    | ~ spl4_7
    | spl4_43 ),
    inference(avatar_split_clause,[],[f287,f275,f88,f195])).

fof(f195,plain,
    ( spl4_30
  <=> l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f88,plain,
    ( spl4_7
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f275,plain,
    ( spl4_43
  <=> l1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f287,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl4_7
    | spl4_43 ),
    inference(resolution,[],[f276,f89])).

fof(f89,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f276,plain,
    ( ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | spl4_43 ),
    inference(avatar_component_clause,[],[f275])).

fof(f280,plain,
    ( ~ spl4_43
    | spl4_44
    | ~ spl4_12
    | ~ spl4_23
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f273,f224,f157,f108,f278,f275])).

fof(f108,plain,
    ( spl4_12
  <=> ! [X0] :
        ( ~ v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | v1_xboole_0(u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f157,plain,
    ( spl4_23
  <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f224,plain,
    ( spl4_36
  <=> v2_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f273,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl4_12
    | ~ spl4_23
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f272,f158])).

fof(f158,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f157])).

fof(f272,plain,
    ( ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | v1_xboole_0(u1_struct_0(k1_pre_topc(sK0,sK1)))
    | ~ spl4_12
    | ~ spl4_36 ),
    inference(resolution,[],[f225,f109])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | v1_xboole_0(u1_struct_0(X0)) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f225,plain,
    ( v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f224])).

fof(f271,plain,
    ( ~ spl4_4
    | ~ spl4_6
    | ~ spl4_16
    | spl4_40 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_16
    | spl4_40 ),
    inference(subsumption_resolution,[],[f269,f77])).

fof(f269,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_6
    | ~ spl4_16
    | spl4_40 ),
    inference(subsumption_resolution,[],[f267,f85])).

fof(f267,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_16
    | spl4_40 ),
    inference(resolution,[],[f256,f125])).

fof(f256,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | spl4_40 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl4_40
  <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f257,plain,
    ( ~ spl4_40
    | spl4_1
    | ~ spl4_4
    | spl4_5
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f253,f227,f80,f76,f64,f255])).

fof(f227,plain,
    ( spl4_37
  <=> ! [X0] :
        ( v2_tex_2(sK1,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

% (11598)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f253,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | spl4_1
    | ~ spl4_4
    | spl4_5
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f252,f77])).

fof(f252,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_1
    | spl4_5
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f251,f65])).

fof(f251,plain,
    ( v2_struct_0(sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_5
    | ~ spl4_37 ),
    inference(resolution,[],[f228,f81])).

fof(f228,plain,
    ( ! [X0] :
        ( v2_tex_2(sK1,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f227])).

fof(f250,plain,
    ( spl4_39
    | ~ spl4_15
    | spl4_35 ),
    inference(avatar_split_clause,[],[f231,f221,f120,f248])).

fof(f120,plain,
    ( spl4_15
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v1_tdlat_3(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v1_tdlat_3(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f221,plain,
    ( spl4_35
  <=> v1_tdlat_3(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f231,plain,
    ( ! [X1] :
        ( ~ v1_tdlat_3(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X1)
        | v2_struct_0(X1) )
    | ~ spl4_15
    | spl4_35 ),
    inference(resolution,[],[f222,f121])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( v1_tdlat_3(X1)
        | ~ v1_tdlat_3(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f120])).

fof(f222,plain,
    ( ~ v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | spl4_35 ),
    inference(avatar_component_clause,[],[f221])).

fof(f240,plain,
    ( ~ spl4_4
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f238,f85])).

fof(f238,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_16
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f237,f77])).

fof(f237,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_16
    | ~ spl4_34 ),
    inference(duplicate_literal_removal,[],[f236])).

fof(f236,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_16
    | ~ spl4_34 ),
    inference(resolution,[],[f214,f125])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl4_34
  <=> ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f229,plain,
    ( ~ spl4_35
    | spl4_36
    | spl4_37
    | ~ spl4_22
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f164,f157,f150,f227,f224,f221])).

fof(f150,plain,
    ( spl4_22
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tdlat_3(X1)
        | v2_tex_2(u1_struct_0(X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f164,plain,
    ( ! [X0] :
        ( v2_tex_2(sK1,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(k1_pre_topc(sK0,sK1))
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ v1_tdlat_3(k1_pre_topc(sK0,sK1))
        | v2_struct_0(X0) )
    | ~ spl4_22
    | ~ spl4_23 ),
    inference(superposition,[],[f151,f158])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( v2_tex_2(u1_struct_0(X1),X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tdlat_3(X1)
        | v2_struct_0(X0) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f150])).

fof(f215,plain,
    ( spl4_34
    | ~ spl4_11
    | spl4_30 ),
    inference(avatar_split_clause,[],[f207,f195,f104,f213])).

fof(f104,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_11
    | spl4_30 ),
    inference(resolution,[],[f196,f105])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f196,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl4_30 ),
    inference(avatar_component_clause,[],[f195])).

fof(f163,plain,(
    spl4_24 ),
    inference(avatar_split_clause,[],[f48,f161])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_tex_2)).

fof(f159,plain,
    ( spl4_23
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f153,f142,f84,f157])).

fof(f142,plain,
    ( spl4_20
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f153,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(resolution,[],[f143,f85])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f142])).

fof(f152,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f62,f150])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(subsumption_resolution,[],[f57,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(f144,plain,
    ( spl4_20
    | ~ spl4_4
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f139,f136,f76,f142])).

fof(f136,plain,
    ( spl4_19
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 )
    | ~ spl4_4
    | ~ spl4_19 ),
    inference(resolution,[],[f137,f77])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(k1_pre_topc(X0,X1)) = X1 )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f136])).

fof(f138,plain,(
    spl4_19 ),
    inference(avatar_split_clause,[],[f42,f136])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

% (11594)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f126,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f55,f124])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f122,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f58,f120])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_tdlat_3(X1) ) ),
    inference(subsumption_resolution,[],[f45,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).

fof(f110,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f51,f108])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f106,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f40,f104])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f94,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f53,f92])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f90,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f38,f88])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f86,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f32,f84])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f82,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f33,f80])).

fof(f33,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f37,f76])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f74,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f36,f72])).

fof(f36,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f70,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f35,f68])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f34,f64])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:34:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (11601)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (11608)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (11601)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (11600)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (11597)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (11593)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (11593)Refutation not found, incomplete strategy% (11593)------------------------------
% 0.21/0.49  % (11593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11593)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (11593)Memory used [KB]: 10618
% 0.21/0.49  % (11593)Time elapsed: 0.070 s
% 0.21/0.49  % (11593)------------------------------
% 0.21/0.49  % (11593)------------------------------
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f320,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f66,f70,f74,f78,f82,f86,f90,f94,f106,f110,f122,f126,f138,f144,f152,f159,f163,f215,f229,f240,f250,f257,f271,f280,f289,f301,f312,f319])).
% 0.21/0.49  fof(f319,plain,(
% 0.21/0.49    spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_24 | ~spl4_48),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f316])).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    $false | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_24 | ~spl4_48)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f77,f65,f69,f81,f85,f300,f162])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | v2_tex_2(X1,X0)) ) | ~spl4_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f161])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    spl4_24 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK2(X0,X1),X1) | v2_tex_2(X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.49  fof(f300,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl4_48),
% 0.21/0.49    inference(avatar_component_clause,[],[f299])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    spl4_48 <=> ! [X0] : ~r2_hidden(X0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl4_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ~v2_tex_2(sK1,sK0) | spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl4_5 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    v2_pre_topc(sK0) | ~spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    spl4_2 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ~v2_struct_0(sK0) | spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl4_1 <=> v2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl4_4 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_16 | ~spl4_39),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f311])).
% 0.21/0.49  fof(f311,plain,(
% 0.21/0.49    $false | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_16 | ~spl4_39)),
% 0.21/0.49    inference(subsumption_resolution,[],[f310,f85])).
% 0.21/0.49  fof(f310,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_16 | ~spl4_39)),
% 0.21/0.49    inference(subsumption_resolution,[],[f309,f65])).
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_3 | ~spl4_4 | ~spl4_16 | ~spl4_39)),
% 0.21/0.49    inference(subsumption_resolution,[],[f308,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    v1_tdlat_3(sK0) | ~spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl4_3 <=> v1_tdlat_3(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f308,plain,(
% 0.21/0.49    ~v1_tdlat_3(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | ~spl4_16 | ~spl4_39)),
% 0.21/0.49    inference(subsumption_resolution,[],[f307,f77])).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_16 | ~spl4_39)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f306])).
% 0.21/0.49  % (11607)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_16 | ~spl4_39)),
% 0.21/0.49    inference(resolution,[],[f249,f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl4_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f124])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    spl4_16 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.49  fof(f249,plain,(
% 0.21/0.49    ( ! [X1] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X1) | ~l1_pre_topc(X1) | ~v1_tdlat_3(X1) | v2_struct_0(X1)) ) | ~spl4_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f248])).
% 0.21/0.49  fof(f248,plain,(
% 0.21/0.49    spl4_39 <=> ! [X1] : (~v1_tdlat_3(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X1) | v2_struct_0(X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.21/0.49  fof(f301,plain,(
% 0.21/0.49    spl4_48 | ~spl4_8 | ~spl4_44),
% 0.21/0.49    inference(avatar_split_clause,[],[f290,f278,f92,f299])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl4_8 <=> ! [X1,X0] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    spl4_44 <=> v1_xboole_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | (~spl4_8 | ~spl4_44)),
% 0.21/0.49    inference(resolution,[],[f279,f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) ) | ~spl4_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f92])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    v1_xboole_0(sK1) | ~spl4_44),
% 0.21/0.49    inference(avatar_component_clause,[],[f278])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    ~spl4_30 | ~spl4_7 | spl4_43),
% 0.21/0.49    inference(avatar_split_clause,[],[f287,f275,f88,f195])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    spl4_30 <=> l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    spl4_7 <=> ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    spl4_43 <=> l1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.21/0.49  fof(f287,plain,(
% 0.21/0.49    ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | (~spl4_7 | spl4_43)),
% 0.21/0.49    inference(resolution,[],[f276,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl4_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f88])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    ~l1_struct_0(k1_pre_topc(sK0,sK1)) | spl4_43),
% 0.21/0.49    inference(avatar_component_clause,[],[f275])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    ~spl4_43 | spl4_44 | ~spl4_12 | ~spl4_23 | ~spl4_36),
% 0.21/0.49    inference(avatar_split_clause,[],[f273,f224,f157,f108,f278,f275])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    spl4_12 <=> ! [X0] : (~v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    spl4_23 <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    spl4_36 <=> v2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.49  fof(f273,plain,(
% 0.21/0.49    v1_xboole_0(sK1) | ~l1_struct_0(k1_pre_topc(sK0,sK1)) | (~spl4_12 | ~spl4_23 | ~spl4_36)),
% 0.21/0.49    inference(forward_demodulation,[],[f272,f158])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl4_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f157])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    ~l1_struct_0(k1_pre_topc(sK0,sK1)) | v1_xboole_0(u1_struct_0(k1_pre_topc(sK0,sK1))) | (~spl4_12 | ~spl4_36)),
% 0.21/0.49    inference(resolution,[],[f225,f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))) ) | ~spl4_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f108])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    v2_struct_0(k1_pre_topc(sK0,sK1)) | ~spl4_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f224])).
% 0.21/0.49  fof(f271,plain,(
% 0.21/0.49    ~spl4_4 | ~spl4_6 | ~spl4_16 | spl4_40),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f270])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    $false | (~spl4_4 | ~spl4_6 | ~spl4_16 | spl4_40)),
% 0.21/0.49    inference(subsumption_resolution,[],[f269,f77])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | (~spl4_6 | ~spl4_16 | spl4_40)),
% 0.21/0.49    inference(subsumption_resolution,[],[f267,f85])).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_16 | spl4_40)),
% 0.21/0.49    inference(resolution,[],[f256,f125])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | spl4_40),
% 0.21/0.49    inference(avatar_component_clause,[],[f255])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    spl4_40 <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    ~spl4_40 | spl4_1 | ~spl4_4 | spl4_5 | ~spl4_37),
% 0.21/0.49    inference(avatar_split_clause,[],[f253,f227,f80,f76,f64,f255])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    spl4_37 <=> ! [X0] : (v2_tex_2(sK1,X0) | v2_struct_0(X0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.49  % (11598)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | (spl4_1 | ~spl4_4 | spl4_5 | ~spl4_37)),
% 0.21/0.49    inference(subsumption_resolution,[],[f252,f77])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | (spl4_1 | spl4_5 | ~spl4_37)),
% 0.21/0.49    inference(subsumption_resolution,[],[f251,f65])).
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | (spl4_5 | ~spl4_37)),
% 0.21/0.49    inference(resolution,[],[f228,f81])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    ( ! [X0] : (v2_tex_2(sK1,X0) | v2_struct_0(X0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | ~spl4_37),
% 0.21/0.49    inference(avatar_component_clause,[],[f227])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    spl4_39 | ~spl4_15 | spl4_35),
% 0.21/0.49    inference(avatar_split_clause,[],[f231,f221,f120,f248])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl4_15 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_tdlat_3(X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    spl4_35 <=> v1_tdlat_3(k1_pre_topc(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_tdlat_3(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X1) | v2_struct_0(X1)) ) | (~spl4_15 | spl4_35)),
% 0.21/0.49    inference(resolution,[],[f222,f121])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0)) ) | ~spl4_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f120])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ~v1_tdlat_3(k1_pre_topc(sK0,sK1)) | spl4_35),
% 0.21/0.49    inference(avatar_component_clause,[],[f221])).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    ~spl4_4 | ~spl4_6 | ~spl4_16 | ~spl4_34),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f239])).
% 0.21/0.49  fof(f239,plain,(
% 0.21/0.49    $false | (~spl4_4 | ~spl4_6 | ~spl4_16 | ~spl4_34)),
% 0.21/0.49    inference(subsumption_resolution,[],[f238,f85])).
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | ~spl4_16 | ~spl4_34)),
% 0.21/0.49    inference(subsumption_resolution,[],[f237,f77])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_16 | ~spl4_34)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f236])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_16 | ~spl4_34)),
% 0.21/0.49    inference(resolution,[],[f214,f125])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | ~spl4_34),
% 0.21/0.49    inference(avatar_component_clause,[],[f213])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    spl4_34 <=> ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    ~spl4_35 | spl4_36 | spl4_37 | ~spl4_22 | ~spl4_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f164,f157,f150,f227,f224,f221])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    spl4_22 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ( ! [X0] : (v2_tex_2(sK1,X0) | ~l1_pre_topc(X0) | v2_struct_0(k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~v1_tdlat_3(k1_pre_topc(sK0,sK1)) | v2_struct_0(X0)) ) | (~spl4_22 | ~spl4_23)),
% 0.21/0.50    inference(superposition,[],[f151,f158])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~v1_tdlat_3(X1) | v2_struct_0(X0)) ) | ~spl4_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f150])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    spl4_34 | ~spl4_11 | spl4_30),
% 0.21/0.50    inference(avatar_split_clause,[],[f207,f195,f104,f213])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl4_11 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | (~spl4_11 | spl4_30)),
% 0.21/0.50    inference(resolution,[],[f196,f105])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl4_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f104])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | spl4_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f195])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    spl4_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f161])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK2(X0,X1),X1) | v2_tex_2(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) | ? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))) => v2_tex_2(X1,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_tex_2)).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    spl4_23 | ~spl4_6 | ~spl4_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f153,f142,f84,f157])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    spl4_20 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(k1_pre_topc(sK0,X0)) = X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | (~spl4_6 | ~spl4_20)),
% 0.21/0.50    inference(resolution,[],[f143,f85])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(k1_pre_topc(sK0,X0)) = X0) ) | ~spl4_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f142])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    spl4_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f62,f150])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f57,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v1_tdlat_3(X1) | v2_tex_2(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    spl4_20 | ~spl4_4 | ~spl4_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f139,f136,f76,f142])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl4_19 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(k1_pre_topc(sK0,X0)) = X0) ) | (~spl4_4 | ~spl4_19)),
% 0.21/0.50    inference(resolution,[],[f137,f77])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) ) | ~spl4_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    spl4_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f136])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  % (11594)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl4_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f55,f124])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl4_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f58,f120])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_tdlat_3(X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f45,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_tdlat_3(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl4_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f51,f108])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f40,f104])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    spl4_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f92])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl4_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f38,f88])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    spl4_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f32,f84])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.21/0.50    inference(negated_conjecture,[],[f12])).
% 0.21/0.50  fof(f12,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ~spl4_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f80])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ~v2_tex_2(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    spl4_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f37,f76])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f36,f72])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    v1_tdlat_3(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f35,f68])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ~spl4_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f64])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (11601)------------------------------
% 0.21/0.50  % (11601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11601)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (11601)Memory used [KB]: 10746
% 0.21/0.50  % (11601)Time elapsed: 0.070 s
% 0.21/0.50  % (11601)------------------------------
% 0.21/0.50  % (11601)------------------------------
% 0.21/0.50  % (11591)Success in time 0.135 s
%------------------------------------------------------------------------------
