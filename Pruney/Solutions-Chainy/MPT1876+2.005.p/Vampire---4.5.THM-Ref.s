%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 314 expanded)
%              Number of leaves         :   26 ( 113 expanded)
%              Depth                    :   14
%              Number of atoms          :  733 (1249 expanded)
%              Number of equality atoms :   15 (  32 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f240,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f99,f104,f113,f122,f132,f157,f164,f169,f184,f202,f212,f221,f232,f235,f239])).

fof(f239,plain,
    ( spl3_7
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | spl3_7
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f224,f97])).

fof(f97,plain,
    ( ~ v1_zfmisc_1(sK1)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_7
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f224,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f223,f131])).

fof(f131,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl3_11
  <=> sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f223,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f222,f155])).

fof(f155,plain,
    ( l1_struct_0(sK2(sK0,sK1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl3_13
  <=> l1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f222,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl3_12 ),
    inference(resolution,[],[f152,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f152,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl3_12
  <=> v7_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f235,plain,
    ( ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f233,f94])).

fof(f94,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_6
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f233,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f34,f98])).

fof(f98,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f34,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f232,plain,
    ( spl3_2
    | ~ spl3_5
    | spl3_6
    | ~ spl3_8
    | spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | spl3_2
    | ~ spl3_5
    | spl3_6
    | ~ spl3_8
    | spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f230,f103])).

fof(f103,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f230,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2
    | ~ spl3_5
    | spl3_6
    | spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f229,f66])).

fof(f66,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f229,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5
    | spl3_6
    | spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f228,f121])).

fof(f121,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_10
  <=> m1_pre_topc(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f228,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5
    | spl3_6
    | spl3_9
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f227,f81])).

fof(f81,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f227,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_6
    | spl3_9
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(resolution,[],[f226,f93])).

fof(f93,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f226,plain,
    ( ! [X3] :
        ( v2_tex_2(sK1,X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK2(sK0,sK1),X3)
        | v2_struct_0(X3)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3))) )
    | spl3_9
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f145,f167])).

fof(f167,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl3_15
  <=> v1_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f145,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK2(sK0,sK1),X3)
        | v2_struct_0(X3)
        | ~ v1_tdlat_3(sK2(sK0,sK1))
        | v2_tex_2(sK1,X3) )
    | spl3_9
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f137,f112])).

fof(f112,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_9
  <=> v2_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f137,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ m1_pre_topc(sK2(sK0,sK1),X3)
        | v2_struct_0(X3)
        | ~ v1_tdlat_3(sK2(sK0,sK1))
        | v2_tex_2(sK1,X3) )
    | ~ spl3_11 ),
    inference(superposition,[],[f57,f131])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(f221,plain,
    ( spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | spl3_15 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | spl3_15 ),
    inference(subsumption_resolution,[],[f219,f103])).

fof(f219,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | spl3_15 ),
    inference(subsumption_resolution,[],[f218,f66])).

fof(f218,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5
    | ~ spl3_6
    | spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | spl3_15 ),
    inference(subsumption_resolution,[],[f217,f121])).

fof(f217,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5
    | ~ spl3_6
    | spl3_9
    | ~ spl3_11
    | spl3_15 ),
    inference(subsumption_resolution,[],[f216,f81])).

fof(f216,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6
    | spl3_9
    | ~ spl3_11
    | spl3_15 ),
    inference(resolution,[],[f94,f208])).

fof(f208,plain,
    ( ! [X1] :
        ( ~ v2_tex_2(sK1,X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | v2_struct_0(X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) )
    | spl3_9
    | ~ spl3_11
    | spl3_15 ),
    inference(subsumption_resolution,[],[f143,f168])).

fof(f168,plain,
    ( ~ v1_tdlat_3(sK2(sK0,sK1))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f166])).

fof(f143,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | v2_struct_0(X1)
        | v1_tdlat_3(sK2(sK0,sK1))
        | ~ v2_tex_2(sK1,X1) )
    | spl3_9
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f135,f112])).

fof(f135,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | v2_struct_0(X1)
        | v1_tdlat_3(sK2(sK0,sK1))
        | ~ v2_tex_2(sK1,X1) )
    | ~ spl3_11 ),
    inference(superposition,[],[f56,f131])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f212,plain,
    ( spl3_9
    | ~ spl3_12
    | ~ spl3_14
    | spl3_15
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl3_9
    | ~ spl3_12
    | ~ spl3_14
    | spl3_15
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f210,f162])).

fof(f162,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl3_14
  <=> l1_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f210,plain,
    ( ~ l1_pre_topc(sK2(sK0,sK1))
    | spl3_9
    | ~ spl3_12
    | spl3_15
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f209,f195])).

fof(f195,plain,
    ( v2_pre_topc(sK2(sK0,sK1))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl3_19
  <=> v2_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f209,plain,
    ( ~ v2_pre_topc(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | spl3_9
    | ~ spl3_12
    | spl3_15 ),
    inference(subsumption_resolution,[],[f185,f152])).

fof(f185,plain,
    ( ~ v7_struct_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | spl3_9
    | spl3_15 ),
    inference(subsumption_resolution,[],[f170,f112])).

fof(f170,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | spl3_15 ),
    inference(resolution,[],[f168,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ v7_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f202,plain,
    ( ~ spl3_3
    | ~ spl3_5
    | ~ spl3_10
    | spl3_19 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_10
    | spl3_19 ),
    inference(subsumption_resolution,[],[f200,f71])).

fof(f71,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f200,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl3_5
    | ~ spl3_10
    | spl3_19 ),
    inference(subsumption_resolution,[],[f199,f81])).

fof(f199,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_10
    | spl3_19 ),
    inference(resolution,[],[f198,f121])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl3_19 ),
    inference(resolution,[],[f196,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f196,plain,
    ( ~ v2_pre_topc(sK2(sK0,sK1))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f194])).

fof(f184,plain,
    ( ~ spl3_5
    | ~ spl3_10
    | spl3_14 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_10
    | spl3_14 ),
    inference(subsumption_resolution,[],[f182,f81])).

fof(f182,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | spl3_14 ),
    inference(resolution,[],[f181,f121])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | spl3_14 ),
    inference(resolution,[],[f163,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f163,plain,
    ( ~ l1_pre_topc(sK2(sK0,sK1))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f161])).

fof(f169,plain,
    ( ~ spl3_15
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_9
    | ~ spl3_10
    | spl3_12 ),
    inference(avatar_split_clause,[],[f159,f150,f119,f110,f79,f74,f69,f64,f166])).

fof(f74,plain,
    ( spl3_4
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f159,plain,
    ( ~ v1_tdlat_3(sK2(sK0,sK1))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_9
    | ~ spl3_10
    | spl3_12 ),
    inference(subsumption_resolution,[],[f127,f151])).

fof(f151,plain,
    ( ~ v7_struct_0(sK2(sK0,sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f150])).

fof(f127,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_9
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f126,f112])).

fof(f126,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(resolution,[],[f121,f108])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v7_struct_0(X0)
        | ~ v1_tdlat_3(X0) )
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f90,f81])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v7_struct_0(X0)
        | ~ v1_tdlat_3(X0) )
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f89,f66])).

fof(f89,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v7_struct_0(X0)
        | ~ v1_tdlat_3(X0) )
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f87,f71])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v7_struct_0(X0)
        | ~ v1_tdlat_3(X0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f76,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | v7_struct_0(X1)
      | ~ v1_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( ~ v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).

fof(f76,plain,
    ( v2_tdlat_3(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f164,plain,
    ( ~ spl3_14
    | spl3_13 ),
    inference(avatar_split_clause,[],[f158,f154,f161])).

fof(f158,plain,
    ( ~ l1_pre_topc(sK2(sK0,sK1))
    | spl3_13 ),
    inference(resolution,[],[f156,f41])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f156,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f157,plain,
    ( spl3_12
    | ~ spl3_13
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f141,f129,f96,f154,f150])).

fof(f141,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f133,f98])).

fof(f133,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ spl3_11 ),
    inference(superposition,[],[f46,f131])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f132,plain,
    ( spl3_11
    | spl3_1
    | spl3_2
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f125,f101,f79,f64,f59,f129])).

fof(f59,plain,
    ( spl3_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f125,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | spl3_1
    | spl3_2
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f124,f81])).

fof(f124,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1))
    | spl3_1
    | spl3_2
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f123,f66])).

fof(f123,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1))
    | spl3_1
    | ~ spl3_8 ),
    inference(resolution,[],[f85,f103])).

fof(f85,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X2)
        | sK1 = u1_struct_0(sK2(X2,sK1)) )
    | spl3_1 ),
    inference(resolution,[],[f61,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f61,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f122,plain,
    ( spl3_10
    | spl3_1
    | spl3_2
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f117,f101,f79,f64,f59,f119])).

fof(f117,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | spl3_1
    | spl3_2
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f116,f81])).

fof(f116,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | spl3_1
    | spl3_2
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f115,f66])).

fof(f115,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | spl3_1
    | ~ spl3_8 ),
    inference(resolution,[],[f84,f103])).

fof(f84,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X1)
        | m1_pre_topc(sK2(X1,sK1),X1) )
    | spl3_1 ),
    inference(resolution,[],[f61,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f113,plain,
    ( ~ spl3_9
    | spl3_1
    | spl3_2
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f107,f101,f79,f64,f59,f110])).

fof(f107,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | spl3_1
    | spl3_2
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f106,f81])).

fof(f106,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | spl3_1
    | spl3_2
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f105,f66])).

fof(f105,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | spl3_1
    | ~ spl3_8 ),
    inference(resolution,[],[f83,f103])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_struct_0(sK2(X0,sK1)) )
    | spl3_1 ),
    inference(resolution,[],[f61,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f104,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f36,f101])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f99,plain,
    ( spl3_6
    | spl3_7 ),
    inference(avatar_split_clause,[],[f33,f96,f92])).

fof(f33,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f82,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f40,f79])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f77,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f38,f69])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f67,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f37,f64])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f35,f59])).

fof(f35,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:48:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (22793)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (22788)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (22788)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f99,f104,f113,f122,f132,f157,f164,f169,f184,f202,f212,f221,f232,f235,f239])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    spl3_7 | ~spl3_11 | ~spl3_12 | ~spl3_13),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f238])).
% 0.21/0.48  fof(f238,plain,(
% 0.21/0.48    $false | (spl3_7 | ~spl3_11 | ~spl3_12 | ~spl3_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f224,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK1) | spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl3_7 <=> v1_zfmisc_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f224,plain,(
% 0.21/0.48    v1_zfmisc_1(sK1) | (~spl3_11 | ~spl3_12 | ~spl3_13)),
% 0.21/0.48    inference(forward_demodulation,[],[f223,f131])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl3_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f129])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl3_11 <=> sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1))) | (~spl3_12 | ~spl3_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f222,f155])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    l1_struct_0(sK2(sK0,sK1)) | ~spl3_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f154])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    spl3_13 <=> l1_struct_0(sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.48  fof(f222,plain,(
% 0.21/0.48    ~l1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1))) | ~spl3_12),
% 0.21/0.48    inference(resolution,[],[f152,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    v7_struct_0(sK2(sK0,sK1)) | ~spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f150])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    spl3_12 <=> v7_struct_0(sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    ~spl3_6 | ~spl3_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f234])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    $false | (~spl3_6 | ~spl3_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f233,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    v2_tex_2(sK1,sK0) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl3_6 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | ~spl3_7),
% 0.21/0.48    inference(subsumption_resolution,[],[f34,f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    v1_zfmisc_1(sK1) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f96])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f11])).
% 0.21/0.48  fof(f11,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    spl3_2 | ~spl3_5 | spl3_6 | ~spl3_8 | spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_15),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f231])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    $false | (spl3_2 | ~spl3_5 | spl3_6 | ~spl3_8 | spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f230,f103])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl3_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_2 | ~spl3_5 | spl3_6 | spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f229,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ~v2_struct_0(sK0) | spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl3_2 <=> v2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_5 | spl3_6 | spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f228,f121])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    m1_pre_topc(sK2(sK0,sK1),sK0) | ~spl3_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f119])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl3_10 <=> m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    ~m1_pre_topc(sK2(sK0,sK1),sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_5 | spl3_6 | spl3_9 | ~spl3_11 | ~spl3_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f227,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    l1_pre_topc(sK0) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl3_5 <=> l1_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2(sK0,sK1),sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_6 | spl3_9 | ~spl3_11 | ~spl3_15)),
% 0.21/0.48    inference(resolution,[],[f226,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f92])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    ( ! [X3] : (v2_tex_2(sK1,X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(sK2(sK0,sK1),X3) | v2_struct_0(X3) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3)))) ) | (spl3_9 | ~spl3_11 | ~spl3_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f145,f167])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    v1_tdlat_3(sK2(sK0,sK1)) | ~spl3_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f166])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    spl3_15 <=> v1_tdlat_3(sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ( ! [X3] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3) | ~m1_pre_topc(sK2(sK0,sK1),X3) | v2_struct_0(X3) | ~v1_tdlat_3(sK2(sK0,sK1)) | v2_tex_2(sK1,X3)) ) | (spl3_9 | ~spl3_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f137,f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ~v2_struct_0(sK2(sK0,sK1)) | spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f110])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl3_9 <=> v2_struct_0(sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ( ! [X3] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3) | v2_struct_0(sK2(sK0,sK1)) | ~m1_pre_topc(sK2(sK0,sK1),X3) | v2_struct_0(X3) | ~v1_tdlat_3(sK2(sK0,sK1)) | v2_tex_2(sK1,X3)) ) | ~spl3_11),
% 0.21/0.48    inference(superposition,[],[f57,f131])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v1_tdlat_3(X1) | v2_tex_2(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_8 | spl3_9 | ~spl3_10 | ~spl3_11 | spl3_15),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f220])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    $false | (spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_8 | spl3_9 | ~spl3_10 | ~spl3_11 | spl3_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f219,f103])).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_2 | ~spl3_5 | ~spl3_6 | spl3_9 | ~spl3_10 | ~spl3_11 | spl3_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f218,f66])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_5 | ~spl3_6 | spl3_9 | ~spl3_10 | ~spl3_11 | spl3_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f217,f121])).
% 0.21/0.48  fof(f217,plain,(
% 0.21/0.48    ~m1_pre_topc(sK2(sK0,sK1),sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_5 | ~spl3_6 | spl3_9 | ~spl3_11 | spl3_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f216,f81])).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2(sK0,sK1),sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_6 | spl3_9 | ~spl3_11 | spl3_15)),
% 0.21/0.48    inference(resolution,[],[f94,f208])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    ( ! [X1] : (~v2_tex_2(sK1,X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK2(sK0,sK1),X1) | v2_struct_0(X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))) ) | (spl3_9 | ~spl3_11 | spl3_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f143,f168])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    ~v1_tdlat_3(sK2(sK0,sK1)) | spl3_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f166])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK2(sK0,sK1),X1) | v2_struct_0(X1) | v1_tdlat_3(sK2(sK0,sK1)) | ~v2_tex_2(sK1,X1)) ) | (spl3_9 | ~spl3_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f135,f112])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v2_struct_0(sK2(sK0,sK1)) | ~m1_pre_topc(sK2(sK0,sK1),X1) | v2_struct_0(X1) | v1_tdlat_3(sK2(sK0,sK1)) | ~v2_tex_2(sK1,X1)) ) | ~spl3_11),
% 0.21/0.48    inference(superposition,[],[f56,f131])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | v1_tdlat_3(X1) | ~v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v1_tdlat_3(X1) | ~v2_tex_2(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    spl3_9 | ~spl3_12 | ~spl3_14 | spl3_15 | ~spl3_19),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f211])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    $false | (spl3_9 | ~spl3_12 | ~spl3_14 | spl3_15 | ~spl3_19)),
% 0.21/0.48    inference(subsumption_resolution,[],[f210,f162])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    l1_pre_topc(sK2(sK0,sK1)) | ~spl3_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f161])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    spl3_14 <=> l1_pre_topc(sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    ~l1_pre_topc(sK2(sK0,sK1)) | (spl3_9 | ~spl3_12 | spl3_15 | ~spl3_19)),
% 0.21/0.48    inference(subsumption_resolution,[],[f209,f195])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    v2_pre_topc(sK2(sK0,sK1)) | ~spl3_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f194])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    spl3_19 <=> v2_pre_topc(sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    ~v2_pre_topc(sK2(sK0,sK1)) | ~l1_pre_topc(sK2(sK0,sK1)) | (spl3_9 | ~spl3_12 | spl3_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f185,f152])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    ~v7_struct_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK2(sK0,sK1)) | ~l1_pre_topc(sK2(sK0,sK1)) | (spl3_9 | spl3_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f170,f112])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    v2_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK2(sK0,sK1)) | ~l1_pre_topc(sK2(sK0,sK1)) | spl3_15),
% 0.21/0.48    inference(resolution,[],[f168,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0] : (v1_tdlat_3(X0) | v2_struct_0(X0) | ~v7_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) | ~v2_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) | (~v2_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => (v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_1)).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    ~spl3_3 | ~spl3_5 | ~spl3_10 | spl3_19),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f201])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    $false | (~spl3_3 | ~spl3_5 | ~spl3_10 | spl3_19)),
% 0.21/0.48    inference(subsumption_resolution,[],[f200,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    v2_pre_topc(sK0) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl3_3 <=> v2_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | (~spl3_5 | ~spl3_10 | spl3_19)),
% 0.21/0.48    inference(subsumption_resolution,[],[f199,f81])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl3_10 | spl3_19)),
% 0.21/0.48    inference(resolution,[],[f198,f121])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_pre_topc(sK2(sK0,sK1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl3_19),
% 0.21/0.48    inference(resolution,[],[f196,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    ~v2_pre_topc(sK2(sK0,sK1)) | spl3_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f194])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    ~spl3_5 | ~spl3_10 | spl3_14),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f183])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    $false | (~spl3_5 | ~spl3_10 | spl3_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f182,f81])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | (~spl3_10 | spl3_14)),
% 0.21/0.48    inference(resolution,[],[f181,f121])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_pre_topc(sK2(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | spl3_14),
% 0.21/0.48    inference(resolution,[],[f163,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    ~l1_pre_topc(sK2(sK0,sK1)) | spl3_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f161])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    ~spl3_15 | spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | spl3_9 | ~spl3_10 | spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f159,f150,f119,f110,f79,f74,f69,f64,f166])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl3_4 <=> v2_tdlat_3(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    ~v1_tdlat_3(sK2(sK0,sK1)) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | spl3_9 | ~spl3_10 | spl3_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f127,f151])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ~v7_struct_0(sK2(sK0,sK1)) | spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f150])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    v7_struct_0(sK2(sK0,sK1)) | ~v1_tdlat_3(sK2(sK0,sK1)) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | spl3_9 | ~spl3_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f126,f112])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~v1_tdlat_3(sK2(sK0,sK1)) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_10)),
% 0.21/0.48    inference(resolution,[],[f121,f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v7_struct_0(X0) | ~v1_tdlat_3(X0)) ) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f90,f81])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v7_struct_0(X0) | ~v1_tdlat_3(X0)) ) | (spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f89,f66])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v7_struct_0(X0) | ~v1_tdlat_3(X0)) ) | (~spl3_3 | ~spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f87,f71])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v7_struct_0(X0) | ~v1_tdlat_3(X0)) ) | ~spl3_4),
% 0.21/0.48    inference(resolution,[],[f76,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | v7_struct_0(X1) | ~v1_tdlat_3(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    v2_tdlat_3(sK0) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    ~spl3_14 | spl3_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f158,f154,f161])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    ~l1_pre_topc(sK2(sK0,sK1)) | spl3_13),
% 0.21/0.48    inference(resolution,[],[f156,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    ~l1_struct_0(sK2(sK0,sK1)) | spl3_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f154])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    spl3_12 | ~spl3_13 | ~spl3_7 | ~spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f141,f129,f96,f154,f150])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ~l1_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | (~spl3_7 | ~spl3_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f133,f98])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~spl3_11),
% 0.21/0.48    inference(superposition,[],[f46,f131])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    spl3_11 | spl3_1 | spl3_2 | ~spl3_5 | ~spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f125,f101,f79,f64,f59,f129])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl3_1 <=> v1_xboole_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    sK1 = u1_struct_0(sK2(sK0,sK1)) | (spl3_1 | spl3_2 | ~spl3_5 | ~spl3_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f124,f81])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | sK1 = u1_struct_0(sK2(sK0,sK1)) | (spl3_1 | spl3_2 | ~spl3_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f123,f66])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | sK1 = u1_struct_0(sK2(sK0,sK1)) | (spl3_1 | ~spl3_8)),
% 0.21/0.48    inference(resolution,[],[f85,f103])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X2] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2))) | v2_struct_0(X2) | ~l1_pre_topc(X2) | sK1 = u1_struct_0(sK2(X2,sK1))) ) | spl3_1),
% 0.21/0.48    inference(resolution,[],[f61,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f59])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    spl3_10 | spl3_1 | spl3_2 | ~spl3_5 | ~spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f117,f101,f79,f64,f59,f119])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    m1_pre_topc(sK2(sK0,sK1),sK0) | (spl3_1 | spl3_2 | ~spl3_5 | ~spl3_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f116,f81])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | m1_pre_topc(sK2(sK0,sK1),sK0) | (spl3_1 | spl3_2 | ~spl3_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f115,f66])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | m1_pre_topc(sK2(sK0,sK1),sK0) | (spl3_1 | ~spl3_8)),
% 0.21/0.48    inference(resolution,[],[f84,f103])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) | v2_struct_0(X1) | ~l1_pre_topc(X1) | m1_pre_topc(sK2(X1,sK1),X1)) ) | spl3_1),
% 0.21/0.48    inference(resolution,[],[f61,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK2(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ~spl3_9 | spl3_1 | spl3_2 | ~spl3_5 | ~spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f107,f101,f79,f64,f59,f110])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ~v2_struct_0(sK2(sK0,sK1)) | (spl3_1 | spl3_2 | ~spl3_5 | ~spl3_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f106,f81])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_struct_0(sK2(sK0,sK1)) | (spl3_1 | spl3_2 | ~spl3_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f105,f66])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_struct_0(sK2(sK0,sK1)) | (spl3_1 | ~spl3_8)),
% 0.21/0.48    inference(resolution,[],[f83,f103])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_struct_0(sK2(X0,sK1))) ) | spl3_1),
% 0.21/0.48    inference(resolution,[],[f61,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_struct_0(sK2(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f101])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl3_6 | spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f96,f92])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f79])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f39,f74])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    v2_tdlat_3(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f38,f69])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f37,f64])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f59])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (22788)------------------------------
% 0.21/0.48  % (22788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22788)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (22788)Memory used [KB]: 10746
% 0.21/0.48  % (22788)Time elapsed: 0.072 s
% 0.21/0.48  % (22788)------------------------------
% 0.21/0.48  % (22788)------------------------------
% 0.21/0.49  % (22784)Success in time 0.135 s
%------------------------------------------------------------------------------
