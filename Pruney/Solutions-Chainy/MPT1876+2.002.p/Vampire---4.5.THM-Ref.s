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
% DateTime   : Thu Dec  3 13:21:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 305 expanded)
%              Number of leaves         :   32 ( 105 expanded)
%              Depth                    :   14
%              Number of atoms          :  710 (1146 expanded)
%              Number of equality atoms :   12 (  26 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f255,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f111,f116,f125,f130,f157,f170,f179,f194,f198,f208,f220,f224,f229,f236,f244,f251,f254])).

fof(f254,plain,
    ( ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f252,f110])).

fof(f110,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_7
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f252,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f45,f106])).

fof(f106,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl2_6
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f45,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f251,plain,
    ( spl2_7
    | ~ spl2_10
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | spl2_7
    | ~ spl2_10
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f249,f109])).

fof(f109,plain,
    ( ~ v1_zfmisc_1(sK1)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f249,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl2_10
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f248,f129])).

fof(f129,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl2_10
  <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f248,plain,
    ( v1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f245,f177])).

fof(f177,plain,
    ( l1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl2_17
  <=> l1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f245,plain,
    ( ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))
    | ~ spl2_16 ),
    inference(resolution,[],[f174,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f174,plain,
    ( v7_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl2_16
  <=> v7_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f244,plain,
    ( ~ spl2_13
    | ~ spl2_15
    | spl2_16
    | ~ spl2_18
    | spl2_19 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl2_13
    | ~ spl2_15
    | spl2_16
    | ~ spl2_18
    | spl2_19 ),
    inference(subsumption_resolution,[],[f242,f173])).

fof(f173,plain,
    ( ~ v7_struct_0(k1_pre_topc(sK0,sK1))
    | spl2_16 ),
    inference(avatar_component_clause,[],[f172])).

fof(f242,plain,
    ( v7_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_13
    | ~ spl2_15
    | ~ spl2_18
    | spl2_19 ),
    inference(subsumption_resolution,[],[f241,f168])).

fof(f168,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl2_15
  <=> l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f241,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | v7_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_13
    | ~ spl2_18
    | spl2_19 ),
    inference(subsumption_resolution,[],[f240,f186])).

fof(f186,plain,
    ( v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl2_18
  <=> v1_tdlat_3(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f240,plain,
    ( ~ v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | v7_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_13
    | spl2_19 ),
    inference(subsumption_resolution,[],[f161,f189])).

fof(f189,plain,
    ( ~ v2_struct_0(k1_pre_topc(sK0,sK1))
    | spl2_19 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl2_19
  <=> v2_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f161,plain,
    ( v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | v7_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f159,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f159,plain,
    ( v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ v2_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | v7_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_13 ),
    inference(resolution,[],[f156,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).

fof(f156,plain,
    ( v2_tdlat_3(k1_pre_topc(sK0,sK1))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl2_13
  <=> v2_tdlat_3(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f236,plain,
    ( spl2_2
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_20 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl2_2
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f234,f94])).

fof(f94,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl2_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f234,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f233,f124])).

fof(f124,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl2_9
  <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f233,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f232,f79])).

fof(f79,plain,
    ( ~ v2_struct_0(sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl2_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f232,plain,
    ( v2_struct_0(sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f231,f115])).

fof(f115,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl2_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f231,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_6
    | ~ spl2_20 ),
    inference(resolution,[],[f193,f106])).

fof(f193,plain,
    ( ! [X3] :
        ( ~ v2_tex_2(sK1,X3)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3)))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X3)
        | ~ l1_pre_topc(X3) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl2_20
  <=> ! [X3] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ v2_tex_2(sK1,X3)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X3)
        | ~ l1_pre_topc(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f229,plain,
    ( ~ spl2_14
    | ~ spl2_15
    | ~ spl2_16
    | spl2_18
    | spl2_19 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_16
    | spl2_18
    | spl2_19 ),
    inference(subsumption_resolution,[],[f227,f185])).

fof(f185,plain,
    ( ~ v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | spl2_18 ),
    inference(avatar_component_clause,[],[f184])).

fof(f227,plain,
    ( v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_16
    | spl2_19 ),
    inference(subsumption_resolution,[],[f226,f189])).

fof(f226,plain,
    ( v2_struct_0(k1_pre_topc(sK0,sK1))
    | v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | ~ spl2_14
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f225,f165])).

fof(f165,plain,
    ( v2_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl2_14
  <=> v2_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f225,plain,
    ( v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ v2_pre_topc(k1_pre_topc(sK0,sK1))
    | v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f210,f168])).

fof(f210,plain,
    ( v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ v2_pre_topc(k1_pre_topc(sK0,sK1))
    | v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | ~ spl2_16 ),
    inference(resolution,[],[f174,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_1)).

fof(f224,plain,
    ( spl2_1
    | ~ spl2_10
    | ~ spl2_17
    | ~ spl2_19 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl2_1
    | ~ spl2_10
    | ~ spl2_17
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f222,f190])).

fof(f190,plain,
    ( v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f188])).

fof(f222,plain,
    ( ~ v2_struct_0(k1_pre_topc(sK0,sK1))
    | spl2_1
    | ~ spl2_10
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f140,f177])).

fof(f140,plain,
    ( ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ v2_struct_0(k1_pre_topc(sK0,sK1))
    | spl2_1
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f133,f74])).

fof(f74,plain,
    ( ~ v1_xboole_0(sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl2_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f133,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_10 ),
    inference(superposition,[],[f65,f129])).

fof(f65,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f220,plain,
    ( spl2_2
    | ~ spl2_5
    | spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_18
    | spl2_19 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | spl2_2
    | ~ spl2_5
    | spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_18
    | spl2_19 ),
    inference(subsumption_resolution,[],[f218,f115])).

fof(f218,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2
    | ~ spl2_5
    | spl2_6
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_18
    | spl2_19 ),
    inference(subsumption_resolution,[],[f217,f79])).

fof(f217,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5
    | spl2_6
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_18
    | spl2_19 ),
    inference(subsumption_resolution,[],[f216,f124])).

fof(f216,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5
    | spl2_6
    | ~ spl2_10
    | ~ spl2_18
    | spl2_19 ),
    inference(subsumption_resolution,[],[f215,f94])).

fof(f215,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_6
    | ~ spl2_10
    | ~ spl2_18
    | spl2_19 ),
    inference(resolution,[],[f214,f105])).

fof(f105,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f214,plain,
    ( ! [X5] :
        ( v2_tex_2(sK1,X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X5)
        | v2_struct_0(X5)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X5))) )
    | ~ spl2_10
    | ~ spl2_18
    | spl2_19 ),
    inference(subsumption_resolution,[],[f213,f186])).

fof(f213,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X5)
        | v2_struct_0(X5)
        | ~ v1_tdlat_3(k1_pre_topc(sK0,sK1))
        | v2_tex_2(sK1,X5) )
    | ~ spl2_10
    | spl2_19 ),
    inference(subsumption_resolution,[],[f138,f189])).

fof(f138,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5)
        | v2_struct_0(k1_pre_topc(sK0,sK1))
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X5)
        | v2_struct_0(X5)
        | ~ v1_tdlat_3(k1_pre_topc(sK0,sK1))
        | v2_tex_2(sK1,X5) )
    | ~ spl2_10 ),
    inference(superposition,[],[f70,f129])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(f208,plain,
    ( ~ spl2_15
    | spl2_17 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl2_15
    | spl2_17 ),
    inference(subsumption_resolution,[],[f180,f168])).

fof(f180,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl2_17 ),
    inference(resolution,[],[f178,f52])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f178,plain,
    ( ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | spl2_17 ),
    inference(avatar_component_clause,[],[f176])).

fof(f198,plain,
    ( ~ spl2_5
    | ~ spl2_9
    | spl2_15 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_9
    | spl2_15 ),
    inference(subsumption_resolution,[],[f196,f94])).

fof(f196,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_9
    | spl2_15 ),
    inference(resolution,[],[f182,f124])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | spl2_15 ),
    inference(resolution,[],[f169,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f169,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f167])).

fof(f194,plain,
    ( spl2_18
    | spl2_19
    | spl2_20
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f136,f127,f192,f188,f184])).

fof(f136,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ l1_pre_topc(X3)
        | v2_struct_0(k1_pre_topc(sK0,sK1))
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X3)
        | v2_struct_0(X3)
        | v1_tdlat_3(k1_pre_topc(sK0,sK1))
        | ~ v2_tex_2(sK1,X3) )
    | ~ spl2_10 ),
    inference(superposition,[],[f69,f129])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f179,plain,
    ( spl2_16
    | ~ spl2_17
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f139,f127,f108,f176,f172])).

fof(f139,plain,
    ( ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | v7_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f132,f110])).

fof(f132,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | v7_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_10 ),
    inference(superposition,[],[f60,f129])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f170,plain,
    ( spl2_14
    | ~ spl2_15
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f160,f154,f167,f163])).

fof(f160,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | v2_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl2_13 ),
    inference(resolution,[],[f156,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f157,plain,
    ( spl2_13
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f152,f122,f92,f87,f82,f77,f154])).

fof(f82,plain,
    ( spl2_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f87,plain,
    ( spl2_4
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f152,plain,
    ( v2_tdlat_3(k1_pre_topc(sK0,sK1))
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(resolution,[],[f151,f124])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_tdlat_3(X0) )
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f100,f94])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_tdlat_3(X0) )
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f99,f79])).

fof(f99,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_tdlat_3(X0) )
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f96,f84])).

fof(f84,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_tdlat_3(X0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f89,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(f89,plain,
    ( v2_tdlat_3(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f130,plain,
    ( spl2_10
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f120,f113,f92,f127])).

fof(f120,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f118,f94])).

fof(f118,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_8 ),
    inference(resolution,[],[f115,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f125,plain,
    ( spl2_9
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f119,f113,f92,f122])).

fof(f119,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f117,f94])).

fof(f117,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl2_8 ),
    inference(resolution,[],[f115,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f116,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f47,f113])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f111,plain,
    ( spl2_6
    | spl2_7 ),
    inference(avatar_split_clause,[],[f44,f108,f104])).

fof(f44,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f95,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f51,f92])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f90,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f50,f87])).

fof(f50,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f49,f82])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f80,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f48,f77])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f46,f72])).

fof(f46,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:00:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (3856)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (3864)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (3864)Refutation not found, incomplete strategy% (3864)------------------------------
% 0.21/0.49  % (3864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3864)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (3864)Memory used [KB]: 6140
% 0.21/0.49  % (3864)Time elapsed: 0.072 s
% 0.21/0.49  % (3864)------------------------------
% 0.21/0.49  % (3864)------------------------------
% 0.21/0.51  % (3854)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (3863)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (3862)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (3868)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (3861)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (3855)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (3873)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (3854)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f255,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f111,f116,f125,f130,f157,f170,f179,f194,f198,f208,f220,f224,f229,f236,f244,f251,f254])).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    ~spl2_6 | ~spl2_7),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f253])).
% 0.21/0.52  fof(f253,plain,(
% 0.21/0.52    $false | (~spl2_6 | ~spl2_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f252,f110])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    v1_zfmisc_1(sK1) | ~spl2_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f108])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    spl2_7 <=> v1_zfmisc_1(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | ~spl2_6),
% 0.21/0.52    inference(subsumption_resolution,[],[f45,f106])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    v2_tex_2(sK1,sK0) | ~spl2_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    spl2_6 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f15])).
% 0.21/0.52  fof(f15,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.52  fof(f251,plain,(
% 0.21/0.52    spl2_7 | ~spl2_10 | ~spl2_16 | ~spl2_17),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f250])).
% 0.21/0.52  fof(f250,plain,(
% 0.21/0.52    $false | (spl2_7 | ~spl2_10 | ~spl2_16 | ~spl2_17)),
% 0.21/0.52    inference(subsumption_resolution,[],[f249,f109])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | spl2_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f108])).
% 0.21/0.52  fof(f249,plain,(
% 0.21/0.52    v1_zfmisc_1(sK1) | (~spl2_10 | ~spl2_16 | ~spl2_17)),
% 0.21/0.52    inference(forward_demodulation,[],[f248,f129])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl2_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f127])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    spl2_10 <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.52  fof(f248,plain,(
% 0.21/0.52    v1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))) | (~spl2_16 | ~spl2_17)),
% 0.21/0.52    inference(subsumption_resolution,[],[f245,f177])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    l1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl2_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f176])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    spl2_17 <=> l1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    ~l1_struct_0(k1_pre_topc(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))) | ~spl2_16),
% 0.21/0.52    inference(resolution,[],[f174,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    v7_struct_0(k1_pre_topc(sK0,sK1)) | ~spl2_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f172])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    spl2_16 <=> v7_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    ~spl2_13 | ~spl2_15 | spl2_16 | ~spl2_18 | spl2_19),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f243])).
% 0.21/0.52  fof(f243,plain,(
% 0.21/0.52    $false | (~spl2_13 | ~spl2_15 | spl2_16 | ~spl2_18 | spl2_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f242,f173])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    ~v7_struct_0(k1_pre_topc(sK0,sK1)) | spl2_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f172])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    v7_struct_0(k1_pre_topc(sK0,sK1)) | (~spl2_13 | ~spl2_15 | ~spl2_18 | spl2_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f241,f168])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~spl2_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f167])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    spl2_15 <=> l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.52  fof(f241,plain,(
% 0.21/0.52    ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | v7_struct_0(k1_pre_topc(sK0,sK1)) | (~spl2_13 | ~spl2_18 | spl2_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f240,f186])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    v1_tdlat_3(k1_pre_topc(sK0,sK1)) | ~spl2_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f184])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    spl2_18 <=> v1_tdlat_3(k1_pre_topc(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    ~v1_tdlat_3(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | v7_struct_0(k1_pre_topc(sK0,sK1)) | (~spl2_13 | spl2_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f161,f189])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    ~v2_struct_0(k1_pre_topc(sK0,sK1)) | spl2_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f188])).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    spl2_19 <=> v2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    v2_struct_0(k1_pre_topc(sK0,sK1)) | ~v1_tdlat_3(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | v7_struct_0(k1_pre_topc(sK0,sK1)) | ~spl2_13),
% 0.21/0.52    inference(subsumption_resolution,[],[f159,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    v2_struct_0(k1_pre_topc(sK0,sK1)) | ~v2_pre_topc(k1_pre_topc(sK0,sK1)) | ~v1_tdlat_3(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | v7_struct_0(k1_pre_topc(sK0,sK1)) | ~spl2_13),
% 0.21/0.52    inference(resolution,[],[f156,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_tdlat_3(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v7_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    v2_tdlat_3(k1_pre_topc(sK0,sK1)) | ~spl2_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f154])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    spl2_13 <=> v2_tdlat_3(k1_pre_topc(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    spl2_2 | ~spl2_5 | ~spl2_6 | ~spl2_8 | ~spl2_9 | ~spl2_20),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f235])).
% 0.21/0.52  fof(f235,plain,(
% 0.21/0.52    $false | (spl2_2 | ~spl2_5 | ~spl2_6 | ~spl2_8 | ~spl2_9 | ~spl2_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f234,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    l1_pre_topc(sK0) | ~spl2_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f92])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    spl2_5 <=> l1_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_6 | ~spl2_8 | ~spl2_9 | ~spl2_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f233,f124])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~spl2_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f122])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    spl2_9 <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.52  fof(f233,plain,(
% 0.21/0.52    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_6 | ~spl2_8 | ~spl2_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f232,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ~v2_struct_0(sK0) | spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl2_2 <=> v2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    v2_struct_0(sK0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | (~spl2_6 | ~spl2_8 | ~spl2_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f231,f115])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    spl2_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | (~spl2_6 | ~spl2_20)),
% 0.21/0.52    inference(resolution,[],[f193,f106])).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    ( ! [X3] : (~v2_tex_2(sK1,X3) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3))) | v2_struct_0(X3) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X3) | ~l1_pre_topc(X3)) ) | ~spl2_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f192])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    spl2_20 <=> ! [X3] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3))) | ~v2_tex_2(sK1,X3) | v2_struct_0(X3) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X3) | ~l1_pre_topc(X3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.52  fof(f229,plain,(
% 0.21/0.52    ~spl2_14 | ~spl2_15 | ~spl2_16 | spl2_18 | spl2_19),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f228])).
% 0.21/0.52  fof(f228,plain,(
% 0.21/0.52    $false | (~spl2_14 | ~spl2_15 | ~spl2_16 | spl2_18 | spl2_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f227,f185])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    ~v1_tdlat_3(k1_pre_topc(sK0,sK1)) | spl2_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f184])).
% 0.21/0.52  fof(f227,plain,(
% 0.21/0.52    v1_tdlat_3(k1_pre_topc(sK0,sK1)) | (~spl2_14 | ~spl2_15 | ~spl2_16 | spl2_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f226,f189])).
% 0.21/0.52  fof(f226,plain,(
% 0.21/0.52    v2_struct_0(k1_pre_topc(sK0,sK1)) | v1_tdlat_3(k1_pre_topc(sK0,sK1)) | (~spl2_14 | ~spl2_15 | ~spl2_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f225,f165])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    v2_pre_topc(k1_pre_topc(sK0,sK1)) | ~spl2_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f163])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    spl2_14 <=> v2_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    v2_struct_0(k1_pre_topc(sK0,sK1)) | ~v2_pre_topc(k1_pre_topc(sK0,sK1)) | v1_tdlat_3(k1_pre_topc(sK0,sK1)) | (~spl2_15 | ~spl2_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f210,f168])).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    v2_struct_0(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~v2_pre_topc(k1_pre_topc(sK0,sK1)) | v1_tdlat_3(k1_pre_topc(sK0,sK1)) | ~spl2_16),
% 0.21/0.52    inference(resolution,[],[f174,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0] : (~v7_struct_0(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v1_tdlat_3(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) | ~v2_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) | (~v2_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => (v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_1)).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    spl2_1 | ~spl2_10 | ~spl2_17 | ~spl2_19),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f223])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    $false | (spl2_1 | ~spl2_10 | ~spl2_17 | ~spl2_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f222,f190])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    v2_struct_0(k1_pre_topc(sK0,sK1)) | ~spl2_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f188])).
% 0.21/0.52  fof(f222,plain,(
% 0.21/0.52    ~v2_struct_0(k1_pre_topc(sK0,sK1)) | (spl2_1 | ~spl2_10 | ~spl2_17)),
% 0.21/0.52    inference(subsumption_resolution,[],[f140,f177])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    ~l1_struct_0(k1_pre_topc(sK0,sK1)) | ~v2_struct_0(k1_pre_topc(sK0,sK1)) | (spl2_1 | ~spl2_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f133,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ~v1_xboole_0(sK1) | spl2_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    spl2_1 <=> v1_xboole_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    v1_xboole_0(sK1) | ~l1_struct_0(k1_pre_topc(sK0,sK1)) | ~v2_struct_0(k1_pre_topc(sK0,sK1)) | ~spl2_10),
% 0.21/0.52    inference(superposition,[],[f65,f129])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).
% 0.21/0.52  fof(f220,plain,(
% 0.21/0.52    spl2_2 | ~spl2_5 | spl2_6 | ~spl2_8 | ~spl2_9 | ~spl2_10 | ~spl2_18 | spl2_19),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f219])).
% 0.21/0.52  fof(f219,plain,(
% 0.21/0.52    $false | (spl2_2 | ~spl2_5 | spl2_6 | ~spl2_8 | ~spl2_9 | ~spl2_10 | ~spl2_18 | spl2_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f218,f115])).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl2_2 | ~spl2_5 | spl2_6 | ~spl2_9 | ~spl2_10 | ~spl2_18 | spl2_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f217,f79])).
% 0.21/0.52  fof(f217,plain,(
% 0.21/0.52    v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_5 | spl2_6 | ~spl2_9 | ~spl2_10 | ~spl2_18 | spl2_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f216,f124])).
% 0.21/0.52  fof(f216,plain,(
% 0.21/0.52    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_5 | spl2_6 | ~spl2_10 | ~spl2_18 | spl2_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f215,f94])).
% 0.21/0.52  fof(f215,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl2_6 | ~spl2_10 | ~spl2_18 | spl2_19)),
% 0.21/0.52    inference(resolution,[],[f214,f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ~v2_tex_2(sK1,sK0) | spl2_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f104])).
% 0.21/0.52  fof(f214,plain,(
% 0.21/0.52    ( ! [X5] : (v2_tex_2(sK1,X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X5) | v2_struct_0(X5) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X5)))) ) | (~spl2_10 | ~spl2_18 | spl2_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f213,f186])).
% 0.21/0.52  fof(f213,plain,(
% 0.21/0.52    ( ! [X5] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X5))) | ~l1_pre_topc(X5) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X5) | v2_struct_0(X5) | ~v1_tdlat_3(k1_pre_topc(sK0,sK1)) | v2_tex_2(sK1,X5)) ) | (~spl2_10 | spl2_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f138,f189])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    ( ! [X5] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X5))) | ~l1_pre_topc(X5) | v2_struct_0(k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X5) | v2_struct_0(X5) | ~v1_tdlat_3(k1_pre_topc(sK0,sK1)) | v2_tex_2(sK1,X5)) ) | ~spl2_10),
% 0.21/0.52    inference(superposition,[],[f70,f129])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v1_tdlat_3(X1) | v2_tex_2(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    ~spl2_15 | spl2_17),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f207])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    $false | (~spl2_15 | spl2_17)),
% 0.21/0.52    inference(subsumption_resolution,[],[f180,f168])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | spl2_17),
% 0.21/0.52    inference(resolution,[],[f178,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    ~l1_struct_0(k1_pre_topc(sK0,sK1)) | spl2_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f176])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    ~spl2_5 | ~spl2_9 | spl2_15),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f197])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    $false | (~spl2_5 | ~spl2_9 | spl2_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f196,f94])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | (~spl2_9 | spl2_15)),
% 0.21/0.52    inference(resolution,[],[f182,f124])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | spl2_15),
% 0.21/0.52    inference(resolution,[],[f169,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | spl2_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f167])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    spl2_18 | spl2_19 | spl2_20 | ~spl2_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f136,f127,f192,f188,f184])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    ( ! [X3] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3) | v2_struct_0(k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X3) | v2_struct_0(X3) | v1_tdlat_3(k1_pre_topc(sK0,sK1)) | ~v2_tex_2(sK1,X3)) ) | ~spl2_10),
% 0.21/0.52    inference(superposition,[],[f69,f129])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | v1_tdlat_3(X1) | ~v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v1_tdlat_3(X1) | ~v2_tex_2(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    spl2_16 | ~spl2_17 | ~spl2_7 | ~spl2_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f139,f127,f108,f176,f172])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ~l1_struct_0(k1_pre_topc(sK0,sK1)) | v7_struct_0(k1_pre_topc(sK0,sK1)) | (~spl2_7 | ~spl2_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f132,f110])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | ~l1_struct_0(k1_pre_topc(sK0,sK1)) | v7_struct_0(k1_pre_topc(sK0,sK1)) | ~spl2_10),
% 0.21/0.52    inference(superposition,[],[f60,f129])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    spl2_14 | ~spl2_15 | ~spl2_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f160,f154,f167,f163])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | v2_pre_topc(k1_pre_topc(sK0,sK1)) | ~spl2_13),
% 0.21/0.52    inference(resolution,[],[f156,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    spl2_13 | spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f152,f122,f92,f87,f82,f77,f154])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl2_3 <=> v2_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    spl2_4 <=> v2_tdlat_3(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    v2_tdlat_3(k1_pre_topc(sK0,sK1)) | (spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_9)),
% 0.21/0.52    inference(resolution,[],[f151,f124])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_tdlat_3(X0)) ) | (spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f100,f94])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_tdlat_3(X0)) ) | (spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f99,f79])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_tdlat_3(X0)) ) | (~spl2_3 | ~spl2_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f96,f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    v2_pre_topc(sK0) | ~spl2_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f82])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_tdlat_3(X0)) ) | ~spl2_4),
% 0.21/0.52    inference(resolution,[],[f89,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_tdlat_3(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    v2_tdlat_3(sK0) | ~spl2_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f87])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    spl2_10 | ~spl2_5 | ~spl2_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f120,f113,f92,f127])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | (~spl2_5 | ~spl2_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f118,f94])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl2_8),
% 0.21/0.52    inference(resolution,[],[f115,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    spl2_9 | ~spl2_5 | ~spl2_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f119,f113,f92,f122])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | (~spl2_5 | ~spl2_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f117,f94])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~spl2_8),
% 0.21/0.52    inference(resolution,[],[f115,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    spl2_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f47,f113])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    spl2_6 | spl2_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f44,f108,f104])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    spl2_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f51,f92])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    spl2_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f50,f87])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    v2_tdlat_3(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    spl2_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f49,f82])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ~spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f48,f77])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ~spl2_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f46,f72])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ~v1_xboole_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (3854)------------------------------
% 0.21/0.52  % (3854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3854)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (3854)Memory used [KB]: 10746
% 0.21/0.52  % (3854)Time elapsed: 0.084 s
% 0.21/0.52  % (3854)------------------------------
% 0.21/0.52  % (3854)------------------------------
% 0.21/0.52  % (3859)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.53  % (3862)Refutation not found, incomplete strategy% (3862)------------------------------
% 0.21/0.53  % (3862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3862)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3862)Memory used [KB]: 6268
% 0.21/0.53  % (3862)Time elapsed: 0.080 s
% 0.21/0.53  % (3862)------------------------------
% 0.21/0.53  % (3862)------------------------------
% 0.21/0.53  % (3848)Success in time 0.159 s
%------------------------------------------------------------------------------
