%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 334 expanded)
%              Number of leaves         :   39 ( 146 expanded)
%              Depth                    :   13
%              Number of atoms          :  632 (1407 expanded)
%              Number of equality atoms :   43 (  92 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f275,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f83,f87,f91,f95,f99,f103,f111,f117,f121,f131,f143,f165,f176,f206,f213,f214,f230,f232,f243,f248,f257,f262,f269,f274])).

fof(f274,plain,(
    spl4_27 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | spl4_27 ),
    inference(resolution,[],[f268,f104])).

fof(f104,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f54,f53])).

fof(f53,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f268,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl4_27 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl4_27
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f269,plain,
    ( spl4_7
    | ~ spl4_6
    | ~ spl4_5
    | ~ spl4_4
    | ~ spl4_27
    | ~ spl4_8
    | spl4_24 ),
    inference(avatar_split_clause,[],[f265,f241,f109,f267,f89,f93,f97,f101])).

fof(f101,plain,
    ( spl4_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f97,plain,
    ( spl4_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f93,plain,
    ( spl4_5
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f89,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f109,plain,
    ( spl4_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f241,plain,
    ( spl4_24
  <=> v2_tex_2(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f265,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_8
    | spl4_24 ),
    inference(forward_demodulation,[],[f263,f110])).

fof(f110,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f263,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_24 ),
    inference(resolution,[],[f242,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

% (13675)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f242,plain,
    ( ~ v2_tex_2(k2_struct_0(sK0),sK0)
    | spl4_24 ),
    inference(avatar_component_clause,[],[f241])).

fof(f262,plain,
    ( spl4_23
    | spl4_26 ),
    inference(avatar_split_clause,[],[f258,f255,f238])).

fof(f238,plain,
    ( spl4_23
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f255,plain,
    ( spl4_26
  <=> r2_hidden(sK3(sK1,k2_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f258,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | spl4_26 ),
    inference(resolution,[],[f256,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f256,plain,
    ( ~ r2_hidden(sK3(sK1,k2_struct_0(sK0)),sK1)
    | spl4_26 ),
    inference(avatar_component_clause,[],[f255])).

fof(f257,plain,
    ( ~ spl4_26
    | ~ spl4_9
    | spl4_25 ),
    inference(avatar_split_clause,[],[f252,f246,f115,f255])).

fof(f115,plain,
    ( spl4_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f246,plain,
    ( spl4_25
  <=> r2_hidden(sK3(sK1,k2_struct_0(sK0)),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f252,plain,
    ( ~ r2_hidden(sK3(sK1,k2_struct_0(sK0)),sK1)
    | ~ spl4_9
    | spl4_25 ),
    inference(resolution,[],[f249,f116])).

fof(f116,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(sK3(sK1,k2_struct_0(sK0)),X0) )
    | spl4_25 ),
    inference(resolution,[],[f247,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f247,plain,
    ( ~ r2_hidden(sK3(sK1,k2_struct_0(sK0)),k2_struct_0(sK0))
    | spl4_25 ),
    inference(avatar_component_clause,[],[f246])).

fof(f248,plain,
    ( ~ spl4_25
    | spl4_23 ),
    inference(avatar_split_clause,[],[f244,f238,f246])).

fof(f244,plain,
    ( ~ r2_hidden(sK3(sK1,k2_struct_0(sK0)),k2_struct_0(sK0))
    | spl4_23 ),
    inference(resolution,[],[f239,f72])).

% (13687)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f239,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f238])).

fof(f243,plain,
    ( ~ spl4_23
    | ~ spl4_24
    | spl4_11
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f236,f174,f128,f241,f238])).

fof(f128,plain,
    ( spl4_11
  <=> sK1 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f174,plain,
    ( spl4_16
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | sK1 = X0
        | ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f236,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ v2_tex_2(k2_struct_0(sK0),sK0)
    | ~ r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl4_16 ),
    inference(resolution,[],[f175,f104])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | sK1 = X0
        | ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(sK1,X0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f174])).

fof(f232,plain,(
    ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl4_22 ),
    inference(resolution,[],[f224,f105])).

fof(f105,plain,(
    ! [X1] : ~ v1_subset_1(X1,X1) ),
    inference(global_subsumption,[],[f104,f73])).

fof(f73,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f224,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl4_22
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f230,plain,
    ( spl4_22
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f229,f128,f109,f78,f223])).

fof(f78,plain,
    ( spl4_2
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f229,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f228,f129])).

fof(f129,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f128])).

fof(f228,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f79,f110])).

fof(f79,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f214,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | sK1 != k2_struct_0(sK0)
    | m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f213,plain,
    ( spl4_7
    | ~ spl4_6
    | ~ spl4_5
    | ~ spl4_4
    | ~ spl4_21
    | ~ spl4_8
    | ~ spl4_11
    | spl4_19 ),
    inference(avatar_split_clause,[],[f210,f195,f128,f109,f201,f89,f93,f97,f101])).

fof(f201,plain,
    ( spl4_21
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f195,plain,
    ( spl4_19
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f210,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_8
    | ~ spl4_11
    | spl4_19 ),
    inference(forward_demodulation,[],[f209,f129])).

fof(f209,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_8
    | spl4_19 ),
    inference(forward_demodulation,[],[f207,f110])).

fof(f207,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_19 ),
    inference(resolution,[],[f196,f65])).

fof(f196,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f195])).

fof(f206,plain,
    ( ~ spl4_19
    | ~ spl4_13
    | ~ spl4_21
    | spl4_1
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f204,f163,f128,f75,f201,f141,f195])).

fof(f141,plain,
    ( spl4_13
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f75,plain,
    ( spl4_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f163,plain,
    ( spl4_15
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v3_tex_2(X0,sK0)
        | ~ v1_tops_1(X0,sK0)
        | ~ v2_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f204,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ v1_tops_1(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | spl4_1
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f191,f129])).

fof(f191,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v1_tops_1(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | spl4_1
    | ~ spl4_15 ),
    inference(resolution,[],[f76,f164])).

fof(f164,plain,
    ( ! [X0] :
        ( v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v1_tops_1(X0,sK0)
        | ~ v2_tex_2(X0,sK0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f163])).

fof(f76,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f176,plain,
    ( ~ spl4_1
    | spl4_16
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f171,f115,f109,f89,f174,f75])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(sK1,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ v3_tex_2(sK1,sK0)
        | sK1 = X0 )
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(resolution,[],[f170,f116])).

fof(f170,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ v2_tex_2(X1,sK0)
        | ~ v3_tex_2(X0,sK0)
        | X0 = X1 )
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f169,f110])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ v2_tex_2(X1,sK0)
        | ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | X0 = X1 )
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f168,f110])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | X0 = X1 )
    | ~ spl4_4 ),
    inference(resolution,[],[f60,f90])).

fof(f90,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f37])).

% (13685)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f165,plain,
    ( ~ spl4_6
    | ~ spl4_4
    | spl4_15
    | spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f155,f109,f101,f163,f89,f97])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ v1_tops_1(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v3_tex_2(X0,sK0) )
    | spl4_7
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f154,f110])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v3_tex_2(X0,sK0) )
    | spl4_7 ),
    inference(resolution,[],[f66,f102])).

fof(f102,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

fof(f143,plain,
    ( ~ spl4_4
    | spl4_13
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f138,f128,f141,f89])).

fof(f138,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_11 ),
    inference(superposition,[],[f57,f129])).

fof(f57,plain,(
    ! [X0] :
      ( v1_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_tops_1(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_tops_1)).

fof(f131,plain,
    ( spl4_11
    | spl4_10
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f126,f109,f85,f119,f128])).

fof(f119,plain,
    ( spl4_10
  <=> v1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f85,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f126,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | sK1 = k2_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f125,f110])).

fof(f125,plain,
    ( sK1 = k2_struct_0(sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f122,f110])).

fof(f122,plain,
    ( u1_struct_0(sK0) = sK1
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f68,f86])).

fof(f86,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f121,plain,
    ( ~ spl4_10
    | spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f113,f109,f78,f119])).

fof(f113,plain,
    ( ~ v1_subset_1(sK1,k2_struct_0(sK0))
    | spl4_2
    | ~ spl4_8 ),
    inference(superposition,[],[f82,f110])).

fof(f82,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f117,plain,
    ( spl4_9
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f112,f109,f85,f115])).

fof(f112,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(superposition,[],[f86,f110])).

fof(f111,plain,
    ( spl4_8
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f107,f89,f109])).

fof(f107,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f106,f90])).

fof(f106,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f55,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f103,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f46,f101])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( v1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v3_tex_2(sK1,sK0) )
    & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK0))
            | ~ v3_tex_2(X1,sK0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ( v1_subset_1(X1,u1_struct_0(sK0))
          | ~ v3_tex_2(X1,sK0) )
        & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( v1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v3_tex_2(sK1,sK0) )
      & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

% (13676)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

% (13673)Refutation not found, incomplete strategy% (13673)------------------------------
% (13673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

% (13673)Termination reason: Refutation not found, incomplete strategy

% (13673)Memory used [KB]: 1663
% (13673)Time elapsed: 0.097 s
% (13673)------------------------------
% (13673)------------------------------
fof(f99,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f47,f97])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f95,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f48,f93])).

fof(f48,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f49,f89])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f50,f85])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f51,f78,f75])).

fof(f51,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f52,f78,f75])).

fof(f52,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (13684)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (13700)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (13677)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (13684)Refutation not found, incomplete strategy% (13684)------------------------------
% 0.20/0.51  % (13684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13688)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (13692)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.51  % (13684)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (13684)Memory used [KB]: 10618
% 0.20/0.51  % (13684)Time elapsed: 0.094 s
% 0.20/0.51  % (13684)------------------------------
% 0.20/0.51  % (13684)------------------------------
% 0.20/0.51  % (13680)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (13696)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (13686)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (13679)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (13695)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (13673)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (13692)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f275,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f80,f83,f87,f91,f95,f99,f103,f111,f117,f121,f131,f143,f165,f176,f206,f213,f214,f230,f232,f243,f248,f257,f262,f269,f274])).
% 0.20/0.52  fof(f274,plain,(
% 0.20/0.52    spl4_27),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f273])).
% 0.20/0.52  fof(f273,plain,(
% 0.20/0.52    $false | spl4_27),
% 0.20/0.52    inference(resolution,[],[f268,f104])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f54,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.53  fof(f268,plain,(
% 0.20/0.53    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl4_27),
% 0.20/0.53    inference(avatar_component_clause,[],[f267])).
% 0.20/0.53  fof(f267,plain,(
% 0.20/0.53    spl4_27 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.20/0.53  fof(f269,plain,(
% 0.20/0.53    spl4_7 | ~spl4_6 | ~spl4_5 | ~spl4_4 | ~spl4_27 | ~spl4_8 | spl4_24),
% 0.20/0.53    inference(avatar_split_clause,[],[f265,f241,f109,f267,f89,f93,f97,f101])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    spl4_7 <=> v2_struct_0(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    spl4_6 <=> v2_pre_topc(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    spl4_5 <=> v1_tdlat_3(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    spl4_4 <=> l1_pre_topc(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    spl4_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.53  fof(f241,plain,(
% 0.20/0.53    spl4_24 <=> v2_tex_2(k2_struct_0(sK0),sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.53  fof(f265,plain,(
% 0.20/0.53    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_8 | spl4_24)),
% 0.20/0.53    inference(forward_demodulation,[],[f263,f110])).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f109])).
% 0.20/0.53  fof(f263,plain,(
% 0.20/0.53    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_24),
% 0.20/0.53    inference(resolution,[],[f242,f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  % (13675)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 0.20/0.53  fof(f242,plain,(
% 0.20/0.53    ~v2_tex_2(k2_struct_0(sK0),sK0) | spl4_24),
% 0.20/0.53    inference(avatar_component_clause,[],[f241])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    spl4_23 | spl4_26),
% 0.20/0.53    inference(avatar_split_clause,[],[f258,f255,f238])).
% 0.20/0.53  fof(f238,plain,(
% 0.20/0.53    spl4_23 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.53  fof(f255,plain,(
% 0.20/0.53    spl4_26 <=> r2_hidden(sK3(sK1,k2_struct_0(sK0)),sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.53  fof(f258,plain,(
% 0.20/0.53    r1_tarski(sK1,k2_struct_0(sK0)) | spl4_26),
% 0.20/0.53    inference(resolution,[],[f256,f71])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(rectify,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.53  fof(f256,plain,(
% 0.20/0.53    ~r2_hidden(sK3(sK1,k2_struct_0(sK0)),sK1) | spl4_26),
% 0.20/0.53    inference(avatar_component_clause,[],[f255])).
% 0.20/0.53  fof(f257,plain,(
% 0.20/0.53    ~spl4_26 | ~spl4_9 | spl4_25),
% 0.20/0.53    inference(avatar_split_clause,[],[f252,f246,f115,f255])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    spl4_9 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.53  fof(f246,plain,(
% 0.20/0.53    spl4_25 <=> r2_hidden(sK3(sK1,k2_struct_0(sK0)),k2_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.53  fof(f252,plain,(
% 0.20/0.53    ~r2_hidden(sK3(sK1,k2_struct_0(sK0)),sK1) | (~spl4_9 | spl4_25)),
% 0.20/0.53    inference(resolution,[],[f249,f116])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl4_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f115])).
% 0.20/0.53  fof(f249,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(sK3(sK1,k2_struct_0(sK0)),X0)) ) | spl4_25),
% 0.20/0.53    inference(resolution,[],[f247,f69])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.53  fof(f247,plain,(
% 0.20/0.53    ~r2_hidden(sK3(sK1,k2_struct_0(sK0)),k2_struct_0(sK0)) | spl4_25),
% 0.20/0.53    inference(avatar_component_clause,[],[f246])).
% 0.20/0.53  fof(f248,plain,(
% 0.20/0.53    ~spl4_25 | spl4_23),
% 0.20/0.53    inference(avatar_split_clause,[],[f244,f238,f246])).
% 0.20/0.53  fof(f244,plain,(
% 0.20/0.53    ~r2_hidden(sK3(sK1,k2_struct_0(sK0)),k2_struct_0(sK0)) | spl4_23),
% 0.20/0.53    inference(resolution,[],[f239,f72])).
% 0.20/0.53  % (13687)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f45])).
% 0.20/0.53  fof(f239,plain,(
% 0.20/0.53    ~r1_tarski(sK1,k2_struct_0(sK0)) | spl4_23),
% 0.20/0.53    inference(avatar_component_clause,[],[f238])).
% 0.20/0.53  fof(f243,plain,(
% 0.20/0.53    ~spl4_23 | ~spl4_24 | spl4_11 | ~spl4_16),
% 0.20/0.53    inference(avatar_split_clause,[],[f236,f174,f128,f241,f238])).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    spl4_11 <=> sK1 = k2_struct_0(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.53  fof(f174,plain,(
% 0.20/0.53    spl4_16 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | sK1 = X0 | ~v2_tex_2(X0,sK0) | ~r1_tarski(sK1,X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.53  fof(f236,plain,(
% 0.20/0.53    sK1 = k2_struct_0(sK0) | ~v2_tex_2(k2_struct_0(sK0),sK0) | ~r1_tarski(sK1,k2_struct_0(sK0)) | ~spl4_16),
% 0.20/0.53    inference(resolution,[],[f175,f104])).
% 0.20/0.53  fof(f175,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | sK1 = X0 | ~v2_tex_2(X0,sK0) | ~r1_tarski(sK1,X0)) ) | ~spl4_16),
% 0.20/0.53    inference(avatar_component_clause,[],[f174])).
% 0.20/0.53  fof(f232,plain,(
% 0.20/0.53    ~spl4_22),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f231])).
% 0.20/0.53  fof(f231,plain,(
% 0.20/0.53    $false | ~spl4_22),
% 0.20/0.53    inference(resolution,[],[f224,f105])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    ( ! [X1] : (~v1_subset_1(X1,X1)) )),
% 0.20/0.53    inference(global_subsumption,[],[f104,f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f67])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(nnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.53  fof(f224,plain,(
% 0.20/0.53    v1_subset_1(sK1,sK1) | ~spl4_22),
% 0.20/0.53    inference(avatar_component_clause,[],[f223])).
% 0.20/0.53  fof(f223,plain,(
% 0.20/0.53    spl4_22 <=> v1_subset_1(sK1,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.53  fof(f230,plain,(
% 0.20/0.53    spl4_22 | ~spl4_2 | ~spl4_8 | ~spl4_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f229,f128,f109,f78,f223])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    spl4_2 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    v1_subset_1(sK1,sK1) | (~spl4_2 | ~spl4_8 | ~spl4_11)),
% 0.20/0.53    inference(forward_demodulation,[],[f228,f129])).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    sK1 = k2_struct_0(sK0) | ~spl4_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f128])).
% 0.20/0.53  fof(f228,plain,(
% 0.20/0.53    v1_subset_1(sK1,k2_struct_0(sK0)) | (~spl4_2 | ~spl4_8)),
% 0.20/0.53    inference(forward_demodulation,[],[f79,f110])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f78])).
% 0.20/0.53  fof(f214,plain,(
% 0.20/0.53    u1_struct_0(sK0) != k2_struct_0(sK0) | sK1 != k2_struct_0(sK0) | m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f213,plain,(
% 0.20/0.53    spl4_7 | ~spl4_6 | ~spl4_5 | ~spl4_4 | ~spl4_21 | ~spl4_8 | ~spl4_11 | spl4_19),
% 0.20/0.53    inference(avatar_split_clause,[],[f210,f195,f128,f109,f201,f89,f93,f97,f101])).
% 0.20/0.53  fof(f201,plain,(
% 0.20/0.53    spl4_21 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.53  fof(f195,plain,(
% 0.20/0.53    spl4_19 <=> v2_tex_2(sK1,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.53  fof(f210,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_8 | ~spl4_11 | spl4_19)),
% 0.20/0.53    inference(forward_demodulation,[],[f209,f129])).
% 0.20/0.53  fof(f209,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_8 | spl4_19)),
% 0.20/0.53    inference(forward_demodulation,[],[f207,f110])).
% 0.20/0.53  fof(f207,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_19),
% 0.20/0.53    inference(resolution,[],[f196,f65])).
% 0.20/0.53  fof(f196,plain,(
% 0.20/0.53    ~v2_tex_2(sK1,sK0) | spl4_19),
% 0.20/0.53    inference(avatar_component_clause,[],[f195])).
% 0.20/0.53  fof(f206,plain,(
% 0.20/0.53    ~spl4_19 | ~spl4_13 | ~spl4_21 | spl4_1 | ~spl4_11 | ~spl4_15),
% 0.20/0.53    inference(avatar_split_clause,[],[f204,f163,f128,f75,f201,f141,f195])).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    spl4_13 <=> v1_tops_1(sK1,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    spl4_1 <=> v3_tex_2(sK1,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    spl4_15 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v3_tex_2(X0,sK0) | ~v1_tops_1(X0,sK0) | ~v2_tex_2(X0,sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.53  fof(f204,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~v1_tops_1(sK1,sK0) | ~v2_tex_2(sK1,sK0) | (spl4_1 | ~spl4_11 | ~spl4_15)),
% 0.20/0.53    inference(forward_demodulation,[],[f191,f129])).
% 0.20/0.53  fof(f191,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(sK1,sK0) | ~v2_tex_2(sK1,sK0) | (spl4_1 | ~spl4_15)),
% 0.20/0.53    inference(resolution,[],[f76,f164])).
% 0.20/0.53  fof(f164,plain,(
% 0.20/0.53    ( ! [X0] : (v3_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | ~v2_tex_2(X0,sK0)) ) | ~spl4_15),
% 0.20/0.53    inference(avatar_component_clause,[],[f163])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ~v3_tex_2(sK1,sK0) | spl4_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f75])).
% 0.20/0.53  fof(f176,plain,(
% 0.20/0.53    ~spl4_1 | spl4_16 | ~spl4_4 | ~spl4_8 | ~spl4_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f171,f115,f109,f89,f174,f75])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(sK1,X0) | ~v2_tex_2(X0,sK0) | ~v3_tex_2(sK1,sK0) | sK1 = X0) ) | (~spl4_4 | ~spl4_8 | ~spl4_9)),
% 0.20/0.53    inference(resolution,[],[f170,f116])).
% 0.20/0.53  fof(f170,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~v2_tex_2(X1,sK0) | ~v3_tex_2(X0,sK0) | X0 = X1) ) | (~spl4_4 | ~spl4_8)),
% 0.20/0.53    inference(forward_demodulation,[],[f169,f110])).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~v2_tex_2(X1,sK0) | ~v3_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | X0 = X1) ) | (~spl4_4 | ~spl4_8)),
% 0.20/0.53    inference(forward_demodulation,[],[f168,f110])).
% 0.20/0.53  fof(f168,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | X0 = X1) ) | ~spl4_4),
% 0.20/0.53    inference(resolution,[],[f60,f90])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    l1_pre_topc(sK0) | ~spl4_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f89])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | X1 = X3) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(rectify,[],[f37])).
% 0.20/0.53  % (13685)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.20/0.53  fof(f165,plain,(
% 0.20/0.53    ~spl4_6 | ~spl4_4 | spl4_15 | spl4_7 | ~spl4_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f155,f109,f101,f163,f89,f97])).
% 0.20/0.53  fof(f155,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~v1_tops_1(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_tex_2(X0,sK0)) ) | (spl4_7 | ~spl4_8)),
% 0.20/0.53    inference(forward_demodulation,[],[f154,f110])).
% 0.20/0.53  fof(f154,plain,(
% 0.20/0.53    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_tex_2(X0,sK0)) ) | spl4_7),
% 0.20/0.53    inference(resolution,[],[f66,f102])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    ~v2_struct_0(sK0) | spl4_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f101])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_tex_2(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).
% 0.20/0.53  fof(f143,plain,(
% 0.20/0.53    ~spl4_4 | spl4_13 | ~spl4_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f138,f128,f141,f89])).
% 0.20/0.53  fof(f138,plain,(
% 0.20/0.53    v1_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl4_11),
% 0.20/0.53    inference(superposition,[],[f57,f129])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X0] : (v1_tops_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0] : (v1_tops_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => v1_tops_1(k2_struct_0(X0),X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_tops_1)).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    spl4_11 | spl4_10 | ~spl4_3 | ~spl4_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f126,f109,f85,f119,f128])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    spl4_10 <=> v1_subset_1(sK1,k2_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    v1_subset_1(sK1,k2_struct_0(sK0)) | sK1 = k2_struct_0(sK0) | (~spl4_3 | ~spl4_8)),
% 0.20/0.53    inference(forward_demodulation,[],[f125,f110])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    sK1 = k2_struct_0(sK0) | v1_subset_1(sK1,u1_struct_0(sK0)) | (~spl4_3 | ~spl4_8)),
% 0.20/0.53    inference(forward_demodulation,[],[f122,f110])).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    u1_struct_0(sK0) = sK1 | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_3),
% 0.20/0.53    inference(resolution,[],[f68,f86])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f85])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f41])).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    ~spl4_10 | spl4_2 | ~spl4_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f113,f109,f78,f119])).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    ~v1_subset_1(sK1,k2_struct_0(sK0)) | (spl4_2 | ~spl4_8)),
% 0.20/0.53    inference(superposition,[],[f82,f110])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl4_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f78])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    spl4_9 | ~spl4_3 | ~spl4_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f112,f109,f85,f115])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl4_3 | ~spl4_8)),
% 0.20/0.53    inference(superposition,[],[f86,f110])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    spl4_8 | ~spl4_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f107,f89,f109])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_4),
% 0.20/0.53    inference(resolution,[],[f106,f90])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.53    inference(resolution,[],[f55,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    ~spl4_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f46,f101])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ~v2_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  % (13676)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.53    inference(negated_conjecture,[],[f13])).
% 0.20/0.53  % (13673)Refutation not found, incomplete strategy% (13673)------------------------------
% 0.20/0.53  % (13673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  fof(f13,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).
% 0.20/0.53  % (13673)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13673)Memory used [KB]: 1663
% 0.20/0.53  % (13673)Time elapsed: 0.097 s
% 0.20/0.53  % (13673)------------------------------
% 0.20/0.53  % (13673)------------------------------
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    spl4_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f47,f97])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    v2_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    spl4_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f48,f93])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    v1_tdlat_3(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    spl4_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f49,f89])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    spl4_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f50,f85])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    spl4_1 | ~spl4_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f51,f78,f75])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ~spl4_1 | spl4_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f52,f78,f75])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (13692)------------------------------
% 0.20/0.53  % (13692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13692)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (13692)Memory used [KB]: 10874
% 0.20/0.53  % (13692)Time elapsed: 0.115 s
% 0.20/0.53  % (13692)------------------------------
% 0.20/0.53  % (13692)------------------------------
% 0.20/0.53  % (13678)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (13672)Success in time 0.177 s
%------------------------------------------------------------------------------
