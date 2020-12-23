%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:40 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 300 expanded)
%              Number of leaves         :   45 ( 137 expanded)
%              Depth                    :    8
%              Number of atoms          :  570 (1101 expanded)
%              Number of equality atoms :   24 (  38 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f392,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f115,f116,f134,f191,f204,f226,f227,f240,f245,f299,f305,f310,f315,f320,f325,f326,f336,f343,f344,f375,f382,f391])).

fof(f391,plain,
    ( ~ spl4_47
    | spl4_8
    | ~ spl4_35
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f390,f379,f307,f112,f372])).

fof(f372,plain,
    ( spl4_47
  <=> l1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f112,plain,
    ( spl4_8
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f307,plain,
    ( spl4_35
  <=> sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f379,plain,
    ( spl4_48
  <=> v7_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f390,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | ~ spl4_35
    | ~ spl4_48 ),
    inference(forward_demodulation,[],[f389,f309])).

fof(f309,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f307])).

fof(f389,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl4_48 ),
    inference(resolution,[],[f381,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f381,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f379])).

fof(f382,plain,
    ( spl4_48
    | ~ spl4_40
    | ~ spl4_37
    | ~ spl4_39
    | spl4_38
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f376,f340,f322,f329,f317,f333,f379])).

fof(f333,plain,
    ( spl4_40
  <=> l1_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f317,plain,
    ( spl4_37
  <=> v1_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f329,plain,
    ( spl4_39
  <=> v2_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f322,plain,
    ( spl4_38
  <=> v2_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f340,plain,
    ( spl4_41
  <=> v2_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f376,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ spl4_41 ),
    inference(resolution,[],[f342,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f342,plain,
    ( v2_tdlat_3(sK2(sK0,sK1))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f340])).

fof(f375,plain,
    ( spl4_47
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f370,f333,f372])).

fof(f370,plain,
    ( l1_struct_0(sK2(sK0,sK1))
    | ~ spl4_40 ),
    inference(resolution,[],[f334,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f334,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f333])).

fof(f344,plain,
    ( spl4_40
    | ~ spl4_1
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f338,f312,f78,f333])).

fof(f78,plain,
    ( spl4_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f312,plain,
    ( spl4_36
  <=> m1_pre_topc(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f338,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2(sK0,sK1))
    | ~ spl4_36 ),
    inference(resolution,[],[f314,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f314,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f312])).

fof(f343,plain,
    ( spl4_41
    | spl4_4
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f337,f312,f83,f78,f93,f340])).

fof(f93,plain,
    ( spl4_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f83,plain,
    ( spl4_2
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f337,plain,
    ( ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tdlat_3(sK2(sK0,sK1))
    | ~ spl4_36 ),
    inference(resolution,[],[f314,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_tdlat_3(X1) ) ),
    inference(global_subsumption,[],[f58,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(f58,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f336,plain,
    ( spl4_39
    | ~ spl4_40
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f327,f317,f333,f329])).

fof(f327,plain,
    ( ~ l1_pre_topc(sK2(sK0,sK1))
    | v2_pre_topc(sK2(sK0,sK1))
    | ~ spl4_37 ),
    inference(resolution,[],[f319,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f319,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f317])).

fof(f326,plain,
    ( sK1 != k1_tarski(sK3(sK1))
    | k1_tarski(sK3(sK1)) != k6_domain_1(u1_struct_0(sK0),sK3(sK1))
    | v2_tex_2(sK1,sK0)
    | ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f325,plain,
    ( ~ spl4_38
    | ~ spl4_7
    | spl4_4
    | spl4_6
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f192,f98,f88,f78,f103,f93,f108,f322])).

fof(f108,plain,
    ( spl4_7
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f103,plain,
    ( spl4_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f88,plain,
    ( spl4_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f98,plain,
    ( spl4_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f192,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl4_5 ),
    inference(resolution,[],[f63,f100])).

fof(f100,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v2_struct_0(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

fof(f320,plain,
    ( spl4_37
    | ~ spl4_7
    | spl4_4
    | spl4_6
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f228,f98,f88,f78,f103,f93,f108,f317])).

fof(f228,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl4_5 ),
    inference(resolution,[],[f64,f100])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | v1_tdlat_3(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f315,plain,
    ( spl4_36
    | ~ spl4_7
    | spl4_4
    | spl4_6
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f231,f98,f88,f78,f103,f93,f108,f312])).

fof(f231,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f65,f100])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f310,plain,
    ( spl4_35
    | ~ spl4_7
    | spl4_4
    | spl4_6
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f276,f98,f88,f78,f103,f93,f108,f307])).

fof(f276,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl4_5 ),
    inference(resolution,[],[f66,f100])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f305,plain,
    ( spl4_34
    | spl4_21
    | spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f300,f112,f103,f210,f302])).

fof(f302,plain,
    ( spl4_34
  <=> sK1 = k1_tarski(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f210,plain,
    ( spl4_21
  <=> v1_xboole_0(k1_tarski(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f300,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(k1_tarski(sK3(sK1)))
    | sK1 = k1_tarski(sK3(sK1))
    | ~ spl4_8 ),
    inference(resolution,[],[f157,f113])).

fof(f113,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f157,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | v1_xboole_0(k1_tarski(sK3(X0)))
      | k1_tarski(sK3(X0)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(k1_tarski(sK3(X0)))
      | k1_tarski(sK3(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f55,f127])).

fof(f127,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(sK3(X0)),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f72,f68])).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f299,plain,(
    ~ spl4_21 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | ~ spl4_21 ),
    inference(resolution,[],[f212,f54])).

fof(f54,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f212,plain,
    ( v1_xboole_0(k1_tarski(sK3(sK1)))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f210])).

fof(f245,plain,
    ( spl4_25
    | spl4_15
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f235,f223,f167,f242])).

fof(f242,plain,
    ( spl4_25
  <=> k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f167,plain,
    ( spl4_15
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f223,plain,
    ( spl4_23
  <=> m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f235,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1))
    | ~ spl4_23 ),
    inference(resolution,[],[f225,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f225,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f223])).

fof(f240,plain,
    ( spl4_24
    | spl4_4
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f234,f223,f88,f78,f93,f237])).

fof(f237,plain,
    ( spl4_24
  <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f234,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)
    | ~ spl4_23 ),
    inference(resolution,[],[f225,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f227,plain,
    ( ~ spl4_15
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f221,f201,f167])).

fof(f201,plain,
    ( spl4_19
  <=> r2_hidden(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f221,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_19 ),
    inference(resolution,[],[f203,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f203,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f201])).

fof(f226,plain,
    ( spl4_23
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f220,f201,f223])).

fof(f220,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl4_19 ),
    inference(resolution,[],[f203,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f204,plain,
    ( spl4_19
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f195,f188,f201])).

fof(f188,plain,
    ( spl4_18
  <=> r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f195,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK0))
    | ~ spl4_18 ),
    inference(resolution,[],[f190,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f190,plain,
    ( r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f188])).

fof(f191,plain,
    ( spl4_18
    | spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f184,f131,f103,f188])).

fof(f131,plain,
    ( spl4_10
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f184,plain,
    ( v1_xboole_0(sK1)
    | r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0))
    | ~ spl4_10 ),
    inference(resolution,[],[f138,f133])).

fof(f133,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f138,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | v1_xboole_0(X1)
      | r1_tarski(k1_tarski(sK3(X1)),X2) ) ),
    inference(resolution,[],[f127,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f134,plain,
    ( spl4_10
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f128,f98,f131])).

fof(f128,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_5 ),
    inference(resolution,[],[f75,f100])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f116,plain,
    ( spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f46,f112,f108])).

fof(f46,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f115,plain,
    ( ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f47,f112,f108])).

fof(f47,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f106,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f48,f103])).

fof(f48,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f49,f98])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f96,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f50,f93])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f91,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f51,f88])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f86,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f52,f83])).

fof(f52,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f81,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f53,f78])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:54:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (14452)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (14444)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (14441)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (14439)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.52  % (14439)Refutation not found, incomplete strategy% (14439)------------------------------
% 1.23/0.52  % (14439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (14439)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.52  
% 1.23/0.52  % (14439)Memory used [KB]: 10746
% 1.23/0.52  % (14439)Time elapsed: 0.108 s
% 1.23/0.52  % (14439)------------------------------
% 1.23/0.52  % (14439)------------------------------
% 1.23/0.52  % (14442)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.23/0.52  % (14440)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.23/0.53  % (14457)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.23/0.53  % (14438)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.23/0.53  % (14437)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.23/0.53  % (14460)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.34/0.54  % (14449)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.54  % (14459)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.34/0.54  % (14453)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.54  % (14448)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.34/0.54  % (14462)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.54  % (14443)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.34/0.54  % (14451)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.34/0.54  % (14463)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.54  % (14453)Refutation found. Thanks to Tanya!
% 1.34/0.54  % SZS status Theorem for theBenchmark
% 1.34/0.54  % SZS output start Proof for theBenchmark
% 1.34/0.54  fof(f392,plain,(
% 1.34/0.54    $false),
% 1.34/0.54    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f115,f116,f134,f191,f204,f226,f227,f240,f245,f299,f305,f310,f315,f320,f325,f326,f336,f343,f344,f375,f382,f391])).
% 1.34/0.54  fof(f391,plain,(
% 1.34/0.54    ~spl4_47 | spl4_8 | ~spl4_35 | ~spl4_48),
% 1.34/0.54    inference(avatar_split_clause,[],[f390,f379,f307,f112,f372])).
% 1.34/0.54  fof(f372,plain,(
% 1.34/0.54    spl4_47 <=> l1_struct_0(sK2(sK0,sK1))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 1.34/0.54  fof(f112,plain,(
% 1.34/0.54    spl4_8 <=> v1_zfmisc_1(sK1)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.34/0.54  fof(f307,plain,(
% 1.34/0.54    spl4_35 <=> sK1 = u1_struct_0(sK2(sK0,sK1))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.34/0.54  fof(f379,plain,(
% 1.34/0.54    spl4_48 <=> v7_struct_0(sK2(sK0,sK1))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 1.34/0.54  fof(f390,plain,(
% 1.34/0.54    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | (~spl4_35 | ~spl4_48)),
% 1.34/0.54    inference(forward_demodulation,[],[f389,f309])).
% 1.34/0.54  fof(f309,plain,(
% 1.34/0.54    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl4_35),
% 1.34/0.54    inference(avatar_component_clause,[],[f307])).
% 1.34/0.54  fof(f389,plain,(
% 1.34/0.54    ~l1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1))) | ~spl4_48),
% 1.34/0.54    inference(resolution,[],[f381,f67])).
% 1.34/0.54  fof(f67,plain,(
% 1.34/0.54    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f40])).
% 1.34/0.54  fof(f40,plain,(
% 1.34/0.54    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 1.34/0.54    inference(flattening,[],[f39])).
% 1.34/0.54  fof(f39,plain,(
% 1.34/0.54    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f9])).
% 1.34/0.54  fof(f9,axiom,(
% 1.34/0.54    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 1.34/0.54  fof(f381,plain,(
% 1.34/0.54    v7_struct_0(sK2(sK0,sK1)) | ~spl4_48),
% 1.34/0.54    inference(avatar_component_clause,[],[f379])).
% 1.34/0.54  fof(f382,plain,(
% 1.34/0.54    spl4_48 | ~spl4_40 | ~spl4_37 | ~spl4_39 | spl4_38 | ~spl4_41),
% 1.34/0.54    inference(avatar_split_clause,[],[f376,f340,f322,f329,f317,f333,f379])).
% 1.34/0.54  fof(f333,plain,(
% 1.34/0.54    spl4_40 <=> l1_pre_topc(sK2(sK0,sK1))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.34/0.54  fof(f317,plain,(
% 1.34/0.54    spl4_37 <=> v1_tdlat_3(sK2(sK0,sK1))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.34/0.54  fof(f329,plain,(
% 1.34/0.54    spl4_39 <=> v2_pre_topc(sK2(sK0,sK1))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.34/0.54  fof(f322,plain,(
% 1.34/0.54    spl4_38 <=> v2_struct_0(sK2(sK0,sK1))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.34/0.54  fof(f340,plain,(
% 1.34/0.54    spl4_41 <=> v2_tdlat_3(sK2(sK0,sK1))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.34/0.54  fof(f376,plain,(
% 1.34/0.54    v2_struct_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK2(sK0,sK1)) | ~v1_tdlat_3(sK2(sK0,sK1)) | ~l1_pre_topc(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~spl4_41),
% 1.34/0.54    inference(resolution,[],[f342,f59])).
% 1.34/0.54  fof(f59,plain,(
% 1.34/0.54    ( ! [X0] : (~v2_tdlat_3(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v7_struct_0(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f31])).
% 1.34/0.54  fof(f31,plain,(
% 1.34/0.54    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.34/0.54    inference(flattening,[],[f30])).
% 1.34/0.54  fof(f30,plain,(
% 1.34/0.54    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f13])).
% 1.34/0.54  fof(f13,axiom,(
% 1.34/0.54    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).
% 1.34/0.54  fof(f342,plain,(
% 1.34/0.54    v2_tdlat_3(sK2(sK0,sK1)) | ~spl4_41),
% 1.34/0.54    inference(avatar_component_clause,[],[f340])).
% 1.34/0.54  fof(f375,plain,(
% 1.34/0.54    spl4_47 | ~spl4_40),
% 1.34/0.54    inference(avatar_split_clause,[],[f370,f333,f372])).
% 1.34/0.54  fof(f370,plain,(
% 1.34/0.54    l1_struct_0(sK2(sK0,sK1)) | ~spl4_40),
% 1.34/0.54    inference(resolution,[],[f334,f56])).
% 1.34/0.54  fof(f56,plain,(
% 1.34/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f25])).
% 1.34/0.54  fof(f25,plain,(
% 1.34/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f7])).
% 1.34/0.54  fof(f7,axiom,(
% 1.34/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.34/0.54  fof(f334,plain,(
% 1.34/0.54    l1_pre_topc(sK2(sK0,sK1)) | ~spl4_40),
% 1.34/0.54    inference(avatar_component_clause,[],[f333])).
% 1.34/0.54  fof(f344,plain,(
% 1.34/0.54    spl4_40 | ~spl4_1 | ~spl4_36),
% 1.34/0.54    inference(avatar_split_clause,[],[f338,f312,f78,f333])).
% 1.34/0.54  fof(f78,plain,(
% 1.34/0.54    spl4_1 <=> l1_pre_topc(sK0)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.34/0.54  fof(f312,plain,(
% 1.34/0.54    spl4_36 <=> m1_pre_topc(sK2(sK0,sK1),sK0)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.34/0.54  fof(f338,plain,(
% 1.34/0.54    ~l1_pre_topc(sK0) | l1_pre_topc(sK2(sK0,sK1)) | ~spl4_36),
% 1.34/0.54    inference(resolution,[],[f314,f60])).
% 1.34/0.54  fof(f60,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f32])).
% 1.34/0.54  fof(f32,plain,(
% 1.34/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f8])).
% 1.34/0.54  fof(f8,axiom,(
% 1.34/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.34/0.54  fof(f314,plain,(
% 1.34/0.54    m1_pre_topc(sK2(sK0,sK1),sK0) | ~spl4_36),
% 1.34/0.54    inference(avatar_component_clause,[],[f312])).
% 1.34/0.54  fof(f343,plain,(
% 1.34/0.54    spl4_41 | spl4_4 | ~spl4_1 | ~spl4_2 | ~spl4_36),
% 1.34/0.54    inference(avatar_split_clause,[],[f337,f312,f83,f78,f93,f340])).
% 1.34/0.54  fof(f93,plain,(
% 1.34/0.54    spl4_4 <=> v2_struct_0(sK0)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.34/0.54  fof(f83,plain,(
% 1.34/0.54    spl4_2 <=> v2_tdlat_3(sK0)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.34/0.54  fof(f337,plain,(
% 1.34/0.54    ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tdlat_3(sK2(sK0,sK1)) | ~spl4_36),
% 1.34/0.54    inference(resolution,[],[f314,f117])).
% 1.34/0.54  fof(f117,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_tdlat_3(X1)) )),
% 1.34/0.54    inference(global_subsumption,[],[f58,f61])).
% 1.34/0.54  fof(f61,plain,(
% 1.34/0.54    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_tdlat_3(X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f34])).
% 1.34/0.54  fof(f34,plain,(
% 1.34/0.54    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.34/0.54    inference(flattening,[],[f33])).
% 1.34/0.54  fof(f33,plain,(
% 1.34/0.54    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f14])).
% 1.34/0.54  fof(f14,axiom,(
% 1.34/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).
% 1.34/0.54  fof(f58,plain,(
% 1.34/0.54    ( ! [X0] : (~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f29])).
% 1.34/0.54  fof(f29,plain,(
% 1.34/0.54    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.34/0.54    inference(flattening,[],[f28])).
% 1.34/0.54  fof(f28,plain,(
% 1.34/0.54    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f12])).
% 1.34/0.54  fof(f12,axiom,(
% 1.34/0.54    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 1.34/0.54  fof(f336,plain,(
% 1.34/0.54    spl4_39 | ~spl4_40 | ~spl4_37),
% 1.34/0.54    inference(avatar_split_clause,[],[f327,f317,f333,f329])).
% 1.34/0.54  fof(f327,plain,(
% 1.34/0.54    ~l1_pre_topc(sK2(sK0,sK1)) | v2_pre_topc(sK2(sK0,sK1)) | ~spl4_37),
% 1.34/0.54    inference(resolution,[],[f319,f57])).
% 1.34/0.54  fof(f57,plain,(
% 1.34/0.54    ( ! [X0] : (~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f27])).
% 1.34/0.54  fof(f27,plain,(
% 1.34/0.54    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.34/0.54    inference(flattening,[],[f26])).
% 1.34/0.54  fof(f26,plain,(
% 1.34/0.54    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f11])).
% 1.34/0.54  fof(f11,axiom,(
% 1.34/0.54    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 1.34/0.54  fof(f319,plain,(
% 1.34/0.54    v1_tdlat_3(sK2(sK0,sK1)) | ~spl4_37),
% 1.34/0.54    inference(avatar_component_clause,[],[f317])).
% 1.34/0.54  fof(f326,plain,(
% 1.34/0.54    sK1 != k1_tarski(sK3(sK1)) | k1_tarski(sK3(sK1)) != k6_domain_1(u1_struct_0(sK0),sK3(sK1)) | v2_tex_2(sK1,sK0) | ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)),
% 1.34/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.34/0.54  fof(f325,plain,(
% 1.34/0.54    ~spl4_38 | ~spl4_7 | spl4_4 | spl4_6 | ~spl4_1 | ~spl4_3 | ~spl4_5),
% 1.34/0.54    inference(avatar_split_clause,[],[f192,f98,f88,f78,f103,f93,f108,f322])).
% 1.34/0.54  fof(f108,plain,(
% 1.34/0.54    spl4_7 <=> v2_tex_2(sK1,sK0)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.34/0.54  fof(f103,plain,(
% 1.34/0.54    spl4_6 <=> v1_xboole_0(sK1)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.34/0.54  fof(f88,plain,(
% 1.34/0.54    spl4_3 <=> v2_pre_topc(sK0)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.34/0.54  fof(f98,plain,(
% 1.34/0.54    spl4_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.34/0.54  fof(f192,plain,(
% 1.34/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK2(sK0,sK1)) | ~spl4_5),
% 1.34/0.54    inference(resolution,[],[f63,f100])).
% 1.34/0.54  fof(f100,plain,(
% 1.34/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_5),
% 1.34/0.54    inference(avatar_component_clause,[],[f98])).
% 1.34/0.54  fof(f63,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | ~v2_struct_0(sK2(X0,X1))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f38])).
% 1.34/0.54  fof(f38,plain,(
% 1.34/0.54    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.34/0.54    inference(flattening,[],[f37])).
% 1.34/0.54  fof(f37,plain,(
% 1.34/0.54    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f20])).
% 1.34/0.54  fof(f20,plain,(
% 1.34/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 1.34/0.54    inference(pure_predicate_removal,[],[f16])).
% 1.34/0.54  fof(f16,axiom,(
% 1.34/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).
% 1.34/0.54  fof(f320,plain,(
% 1.34/0.54    spl4_37 | ~spl4_7 | spl4_4 | spl4_6 | ~spl4_1 | ~spl4_3 | ~spl4_5),
% 1.34/0.54    inference(avatar_split_clause,[],[f228,f98,f88,f78,f103,f93,f108,f317])).
% 1.34/0.54  fof(f228,plain,(
% 1.34/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK2(sK0,sK1)) | ~spl4_5),
% 1.34/0.54    inference(resolution,[],[f64,f100])).
% 1.34/0.54  fof(f64,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | v1_tdlat_3(sK2(X0,X1))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f38])).
% 1.34/0.54  fof(f315,plain,(
% 1.34/0.54    spl4_36 | ~spl4_7 | spl4_4 | spl4_6 | ~spl4_1 | ~spl4_3 | ~spl4_5),
% 1.34/0.54    inference(avatar_split_clause,[],[f231,f98,f88,f78,f103,f93,f108,f312])).
% 1.34/0.54  fof(f231,plain,(
% 1.34/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK2(sK0,sK1),sK0) | ~spl4_5),
% 1.34/0.54    inference(resolution,[],[f65,f100])).
% 1.34/0.54  fof(f65,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | m1_pre_topc(sK2(X0,X1),X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f38])).
% 1.34/0.54  fof(f310,plain,(
% 1.34/0.54    spl4_35 | ~spl4_7 | spl4_4 | spl4_6 | ~spl4_1 | ~spl4_3 | ~spl4_5),
% 1.34/0.54    inference(avatar_split_clause,[],[f276,f98,f88,f78,f103,f93,f108,f307])).
% 1.34/0.54  fof(f276,plain,(
% 1.34/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl4_5),
% 1.34/0.54    inference(resolution,[],[f66,f100])).
% 1.34/0.54  fof(f66,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | u1_struct_0(sK2(X0,X1)) = X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f38])).
% 1.34/0.54  fof(f305,plain,(
% 1.34/0.54    spl4_34 | spl4_21 | spl4_6 | ~spl4_8),
% 1.34/0.54    inference(avatar_split_clause,[],[f300,f112,f103,f210,f302])).
% 1.34/0.54  fof(f302,plain,(
% 1.34/0.54    spl4_34 <=> sK1 = k1_tarski(sK3(sK1))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.34/0.54  fof(f210,plain,(
% 1.34/0.54    spl4_21 <=> v1_xboole_0(k1_tarski(sK3(sK1)))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.34/0.54  fof(f300,plain,(
% 1.34/0.54    v1_xboole_0(sK1) | v1_xboole_0(k1_tarski(sK3(sK1))) | sK1 = k1_tarski(sK3(sK1)) | ~spl4_8),
% 1.34/0.54    inference(resolution,[],[f157,f113])).
% 1.34/0.54  fof(f113,plain,(
% 1.34/0.54    v1_zfmisc_1(sK1) | ~spl4_8),
% 1.34/0.54    inference(avatar_component_clause,[],[f112])).
% 1.34/0.54  fof(f157,plain,(
% 1.34/0.54    ( ! [X0] : (~v1_zfmisc_1(X0) | v1_xboole_0(X0) | v1_xboole_0(k1_tarski(sK3(X0))) | k1_tarski(sK3(X0)) = X0) )),
% 1.34/0.54    inference(duplicate_literal_removal,[],[f155])).
% 1.34/0.54  fof(f155,plain,(
% 1.34/0.54    ( ! [X0] : (v1_xboole_0(X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(k1_tarski(sK3(X0))) | k1_tarski(sK3(X0)) = X0 | v1_xboole_0(X0)) )),
% 1.34/0.54    inference(resolution,[],[f55,f127])).
% 1.34/0.54  fof(f127,plain,(
% 1.34/0.54    ( ! [X0] : (r1_tarski(k1_tarski(sK3(X0)),X0) | v1_xboole_0(X0)) )),
% 1.34/0.54    inference(resolution,[],[f72,f68])).
% 1.34/0.54  fof(f68,plain,(
% 1.34/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f1])).
% 1.34/0.54  fof(f1,axiom,(
% 1.34/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.34/0.54  fof(f72,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f4])).
% 1.34/0.54  fof(f4,axiom,(
% 1.34/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.34/0.54  fof(f55,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | v1_xboole_0(X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X0) | X0 = X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f24])).
% 1.34/0.54  fof(f24,plain,(
% 1.34/0.54    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.34/0.54    inference(flattening,[],[f23])).
% 1.34/0.54  fof(f23,plain,(
% 1.34/0.54    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f15])).
% 1.34/0.54  fof(f15,axiom,(
% 1.34/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 1.34/0.54  fof(f299,plain,(
% 1.34/0.54    ~spl4_21),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f298])).
% 1.34/0.54  fof(f298,plain,(
% 1.34/0.54    $false | ~spl4_21),
% 1.34/0.54    inference(resolution,[],[f212,f54])).
% 1.34/0.54  fof(f54,plain,(
% 1.34/0.54    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f3])).
% 1.34/0.54  fof(f3,axiom,(
% 1.34/0.54    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.34/0.54  fof(f212,plain,(
% 1.34/0.54    v1_xboole_0(k1_tarski(sK3(sK1))) | ~spl4_21),
% 1.34/0.54    inference(avatar_component_clause,[],[f210])).
% 1.34/0.54  fof(f245,plain,(
% 1.34/0.54    spl4_25 | spl4_15 | ~spl4_23),
% 1.34/0.54    inference(avatar_split_clause,[],[f235,f223,f167,f242])).
% 1.34/0.54  fof(f242,plain,(
% 1.34/0.54    spl4_25 <=> k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.34/0.54  fof(f167,plain,(
% 1.34/0.54    spl4_15 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.34/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.34/0.55  fof(f223,plain,(
% 1.34/0.55    spl4_23 <=> m1_subset_1(sK3(sK1),u1_struct_0(sK0))),
% 1.34/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.34/0.55  fof(f235,plain,(
% 1.34/0.55    v1_xboole_0(u1_struct_0(sK0)) | k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) | ~spl4_23),
% 1.34/0.55    inference(resolution,[],[f225,f71])).
% 1.34/0.55  fof(f71,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f43])).
% 1.34/0.55  fof(f43,plain,(
% 1.34/0.55    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.34/0.55    inference(flattening,[],[f42])).
% 1.34/0.55  fof(f42,plain,(
% 1.34/0.55    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.34/0.55    inference(ennf_transformation,[],[f10])).
% 1.34/0.55  fof(f10,axiom,(
% 1.34/0.55    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.34/0.55  fof(f225,plain,(
% 1.34/0.55    m1_subset_1(sK3(sK1),u1_struct_0(sK0)) | ~spl4_23),
% 1.34/0.55    inference(avatar_component_clause,[],[f223])).
% 1.34/0.55  fof(f240,plain,(
% 1.34/0.55    spl4_24 | spl4_4 | ~spl4_1 | ~spl4_3 | ~spl4_23),
% 1.34/0.55    inference(avatar_split_clause,[],[f234,f223,f88,f78,f93,f237])).
% 1.34/0.55  fof(f237,plain,(
% 1.34/0.55    spl4_24 <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)),
% 1.34/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.34/0.55  fof(f234,plain,(
% 1.34/0.55    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0) | ~spl4_23),
% 1.34/0.55    inference(resolution,[],[f225,f62])).
% 1.34/0.55  fof(f62,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f36])).
% 1.34/0.55  fof(f36,plain,(
% 1.34/0.55    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.34/0.55    inference(flattening,[],[f35])).
% 1.34/0.55  fof(f35,plain,(
% 1.34/0.55    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.34/0.55    inference(ennf_transformation,[],[f17])).
% 1.34/0.55  fof(f17,axiom,(
% 1.34/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 1.34/0.55  fof(f227,plain,(
% 1.34/0.55    ~spl4_15 | ~spl4_19),
% 1.34/0.55    inference(avatar_split_clause,[],[f221,f201,f167])).
% 1.34/0.55  fof(f201,plain,(
% 1.34/0.55    spl4_19 <=> r2_hidden(sK3(sK1),u1_struct_0(sK0))),
% 1.34/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.34/0.55  fof(f221,plain,(
% 1.34/0.55    ~v1_xboole_0(u1_struct_0(sK0)) | ~spl4_19),
% 1.34/0.55    inference(resolution,[],[f203,f69])).
% 1.34/0.55  fof(f69,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f1])).
% 1.34/0.55  fof(f203,plain,(
% 1.34/0.55    r2_hidden(sK3(sK1),u1_struct_0(sK0)) | ~spl4_19),
% 1.34/0.55    inference(avatar_component_clause,[],[f201])).
% 1.34/0.55  fof(f226,plain,(
% 1.34/0.55    spl4_23 | ~spl4_19),
% 1.34/0.55    inference(avatar_split_clause,[],[f220,f201,f223])).
% 1.34/0.55  fof(f220,plain,(
% 1.34/0.55    m1_subset_1(sK3(sK1),u1_struct_0(sK0)) | ~spl4_19),
% 1.34/0.55    inference(resolution,[],[f203,f70])).
% 1.34/0.55  fof(f70,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f41])).
% 1.34/0.55  fof(f41,plain,(
% 1.34/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.34/0.55    inference(ennf_transformation,[],[f5])).
% 1.34/0.55  fof(f5,axiom,(
% 1.34/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.34/0.55  fof(f204,plain,(
% 1.34/0.55    spl4_19 | ~spl4_18),
% 1.34/0.55    inference(avatar_split_clause,[],[f195,f188,f201])).
% 1.34/0.55  fof(f188,plain,(
% 1.34/0.55    spl4_18 <=> r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0))),
% 1.34/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.34/0.55  fof(f195,plain,(
% 1.34/0.55    r2_hidden(sK3(sK1),u1_struct_0(sK0)) | ~spl4_18),
% 1.34/0.55    inference(resolution,[],[f190,f73])).
% 1.34/0.55  fof(f73,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f4])).
% 1.34/0.55  fof(f190,plain,(
% 1.34/0.55    r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0)) | ~spl4_18),
% 1.34/0.55    inference(avatar_component_clause,[],[f188])).
% 1.34/0.55  fof(f191,plain,(
% 1.34/0.55    spl4_18 | spl4_6 | ~spl4_10),
% 1.34/0.55    inference(avatar_split_clause,[],[f184,f131,f103,f188])).
% 1.34/0.55  fof(f131,plain,(
% 1.34/0.55    spl4_10 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 1.34/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.34/0.55  fof(f184,plain,(
% 1.34/0.55    v1_xboole_0(sK1) | r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0)) | ~spl4_10),
% 1.34/0.55    inference(resolution,[],[f138,f133])).
% 1.34/0.55  fof(f133,plain,(
% 1.34/0.55    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_10),
% 1.34/0.55    inference(avatar_component_clause,[],[f131])).
% 1.34/0.55  fof(f138,plain,(
% 1.34/0.55    ( ! [X2,X1] : (~r1_tarski(X1,X2) | v1_xboole_0(X1) | r1_tarski(k1_tarski(sK3(X1)),X2)) )),
% 1.34/0.55    inference(resolution,[],[f127,f76])).
% 1.34/0.55  fof(f76,plain,(
% 1.34/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f45])).
% 1.34/0.55  fof(f45,plain,(
% 1.34/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.34/0.55    inference(flattening,[],[f44])).
% 1.34/0.55  fof(f44,plain,(
% 1.34/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.34/0.55    inference(ennf_transformation,[],[f2])).
% 1.34/0.55  fof(f2,axiom,(
% 1.34/0.55    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.34/0.55  fof(f134,plain,(
% 1.34/0.55    spl4_10 | ~spl4_5),
% 1.34/0.55    inference(avatar_split_clause,[],[f128,f98,f131])).
% 1.34/0.55  fof(f128,plain,(
% 1.34/0.55    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_5),
% 1.34/0.55    inference(resolution,[],[f75,f100])).
% 1.34/0.55  fof(f75,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f6])).
% 1.34/0.55  fof(f6,axiom,(
% 1.34/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.34/0.55  fof(f116,plain,(
% 1.34/0.55    spl4_7 | spl4_8),
% 1.34/0.55    inference(avatar_split_clause,[],[f46,f112,f108])).
% 1.34/0.55  fof(f46,plain,(
% 1.34/0.55    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 1.34/0.55    inference(cnf_transformation,[],[f22])).
% 1.34/0.55  fof(f22,plain,(
% 1.34/0.55    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.34/0.55    inference(flattening,[],[f21])).
% 1.34/0.55  fof(f21,plain,(
% 1.34/0.55    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.34/0.55    inference(ennf_transformation,[],[f19])).
% 1.34/0.55  fof(f19,negated_conjecture,(
% 1.34/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.34/0.55    inference(negated_conjecture,[],[f18])).
% 1.34/0.55  fof(f18,conjecture,(
% 1.34/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 1.34/0.55  fof(f115,plain,(
% 1.34/0.55    ~spl4_7 | ~spl4_8),
% 1.34/0.55    inference(avatar_split_clause,[],[f47,f112,f108])).
% 1.34/0.55  fof(f47,plain,(
% 1.34/0.55    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 1.34/0.55    inference(cnf_transformation,[],[f22])).
% 1.34/0.55  fof(f106,plain,(
% 1.34/0.55    ~spl4_6),
% 1.34/0.55    inference(avatar_split_clause,[],[f48,f103])).
% 1.34/0.55  fof(f48,plain,(
% 1.34/0.55    ~v1_xboole_0(sK1)),
% 1.34/0.55    inference(cnf_transformation,[],[f22])).
% 1.34/0.55  fof(f101,plain,(
% 1.34/0.55    spl4_5),
% 1.34/0.55    inference(avatar_split_clause,[],[f49,f98])).
% 1.34/0.55  fof(f49,plain,(
% 1.34/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.34/0.55    inference(cnf_transformation,[],[f22])).
% 1.34/0.55  fof(f96,plain,(
% 1.34/0.55    ~spl4_4),
% 1.34/0.55    inference(avatar_split_clause,[],[f50,f93])).
% 1.34/0.55  fof(f50,plain,(
% 1.34/0.55    ~v2_struct_0(sK0)),
% 1.34/0.55    inference(cnf_transformation,[],[f22])).
% 1.34/0.55  fof(f91,plain,(
% 1.34/0.55    spl4_3),
% 1.34/0.55    inference(avatar_split_clause,[],[f51,f88])).
% 1.34/0.55  fof(f51,plain,(
% 1.34/0.55    v2_pre_topc(sK0)),
% 1.34/0.55    inference(cnf_transformation,[],[f22])).
% 1.34/0.55  fof(f86,plain,(
% 1.34/0.55    spl4_2),
% 1.34/0.55    inference(avatar_split_clause,[],[f52,f83])).
% 1.34/0.55  fof(f52,plain,(
% 1.34/0.55    v2_tdlat_3(sK0)),
% 1.34/0.55    inference(cnf_transformation,[],[f22])).
% 1.34/0.55  fof(f81,plain,(
% 1.34/0.55    spl4_1),
% 1.34/0.55    inference(avatar_split_clause,[],[f53,f78])).
% 1.34/0.55  fof(f53,plain,(
% 1.34/0.55    l1_pre_topc(sK0)),
% 1.34/0.55    inference(cnf_transformation,[],[f22])).
% 1.34/0.55  % SZS output end Proof for theBenchmark
% 1.34/0.55  % (14453)------------------------------
% 1.34/0.55  % (14453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (14453)Termination reason: Refutation
% 1.34/0.55  
% 1.34/0.55  % (14453)Memory used [KB]: 11001
% 1.34/0.55  % (14453)Time elapsed: 0.128 s
% 1.34/0.55  % (14453)------------------------------
% 1.34/0.55  % (14453)------------------------------
% 1.34/0.55  % (14455)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.55  % (14446)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.34/0.55  % (14465)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.55  % (14436)Success in time 0.181 s
%------------------------------------------------------------------------------
