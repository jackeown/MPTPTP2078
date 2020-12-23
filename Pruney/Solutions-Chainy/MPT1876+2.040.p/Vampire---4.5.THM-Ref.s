%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 313 expanded)
%              Number of leaves         :   43 ( 140 expanded)
%              Depth                    :    9
%              Number of atoms          :  554 (1143 expanded)
%              Number of equality atoms :   27 (  47 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f798,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f112,f113,f138,f283,f299,f300,f319,f329,f374,f598,f608,f655,f674,f679,f684,f689,f694,f701,f706,f707,f795,f797])).

fof(f797,plain,
    ( spl5_96
    | ~ spl5_79 ),
    inference(avatar_split_clause,[],[f796,f703,f792])).

fof(f792,plain,
    ( spl5_96
  <=> l1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f703,plain,
    ( spl5_79
  <=> l1_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f796,plain,
    ( l1_struct_0(sK2(sK0,sK1))
    | ~ spl5_79 ),
    inference(resolution,[],[f705,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f705,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl5_79 ),
    inference(avatar_component_clause,[],[f703])).

fof(f795,plain,
    ( ~ spl5_96
    | spl5_8
    | ~ spl5_74
    | ~ spl5_78 ),
    inference(avatar_split_clause,[],[f790,f698,f676,f109,f792])).

fof(f109,plain,
    ( spl5_8
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f676,plain,
    ( spl5_74
  <=> sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f698,plain,
    ( spl5_78
  <=> v7_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f790,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | ~ spl5_74
    | ~ spl5_78 ),
    inference(forward_demodulation,[],[f789,f678])).

fof(f678,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f676])).

fof(f789,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl5_78 ),
    inference(resolution,[],[f700,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f700,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ spl5_78 ),
    inference(avatar_component_clause,[],[f698])).

fof(f707,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK3(sK1)) != k1_tarski(sK3(sK1))
    | sK1 != k1_tarski(sK3(sK1))
    | v2_tex_2(sK1,sK0)
    | ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f706,plain,
    ( spl5_79
    | ~ spl5_1
    | ~ spl5_75 ),
    inference(avatar_split_clause,[],[f696,f681,f75,f703])).

fof(f75,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f681,plain,
    ( spl5_75
  <=> m1_pre_topc(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f696,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2(sK0,sK1))
    | ~ spl5_75 ),
    inference(resolution,[],[f683,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f683,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl5_75 ),
    inference(avatar_component_clause,[],[f681])).

fof(f701,plain,
    ( ~ spl5_76
    | spl5_78
    | spl5_77
    | spl5_4
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_75 ),
    inference(avatar_split_clause,[],[f695,f681,f80,f75,f90,f691,f698,f686])).

fof(f686,plain,
    ( spl5_76
  <=> v1_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f691,plain,
    ( spl5_77
  <=> v2_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f90,plain,
    ( spl5_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f80,plain,
    ( spl5_2
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f695,plain,
    ( ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl5_75 ),
    inference(resolution,[],[f683,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | v7_struct_0(X1)
      | ~ v1_tdlat_3(X1) ) ),
    inference(global_subsumption,[],[f52,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f694,plain,
    ( ~ spl5_77
    | ~ spl5_7
    | spl5_4
    | spl5_6
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f249,f95,f85,f75,f100,f90,f105,f691])).

fof(f105,plain,
    ( spl5_7
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f100,plain,
    ( spl5_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f85,plain,
    ( spl5_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f95,plain,
    ( spl5_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f249,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl5_5 ),
    inference(resolution,[],[f56,f97])).

fof(f97,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v2_struct_0(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
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

fof(f689,plain,
    ( spl5_76
    | ~ spl5_7
    | spl5_4
    | spl5_6
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f259,f95,f85,f75,f100,f90,f105,f686])).

fof(f259,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl5_5 ),
    inference(resolution,[],[f57,f97])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | v1_tdlat_3(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f684,plain,
    ( spl5_75
    | ~ spl5_7
    | spl5_4
    | spl5_6
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f267,f95,f85,f75,f100,f90,f105,f681])).

fof(f267,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f58,f97])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f679,plain,
    ( spl5_74
    | ~ spl5_7
    | spl5_4
    | spl5_6
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f285,f95,f85,f75,f100,f90,f105,f676])).

fof(f285,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl5_5 ),
    inference(resolution,[],[f59,f97])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f674,plain,
    ( spl5_73
    | spl5_68
    | ~ spl5_8
    | spl5_6
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f663,f605,f100,f109,f629,f671])).

fof(f671,plain,
    ( spl5_73
  <=> sK1 = k1_tarski(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f629,plain,
    ( spl5_68
  <=> v1_xboole_0(k1_tarski(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f605,plain,
    ( spl5_63
  <=> r1_tarski(k1_tarski(sK3(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f663,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(k1_tarski(sK3(sK1)))
    | sK1 = k1_tarski(sK3(sK1))
    | ~ spl5_63 ),
    inference(resolution,[],[f607,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f607,plain,
    ( r1_tarski(k1_tarski(sK3(sK1)),sK1)
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f605])).

fof(f655,plain,(
    ~ spl5_68 ),
    inference(avatar_contradiction_clause,[],[f651])).

fof(f651,plain,
    ( $false
    | ~ spl5_68 ),
    inference(resolution,[],[f631,f49])).

fof(f49,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f631,plain,
    ( v1_xboole_0(k1_tarski(sK3(sK1)))
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f629])).

fof(f608,plain,
    ( spl5_63
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f599,f595,f605])).

fof(f595,plain,
    ( spl5_62
  <=> m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f599,plain,
    ( r1_tarski(k1_tarski(sK3(sK1)),sK1)
    | ~ spl5_62 ),
    inference(resolution,[],[f597,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f597,plain,
    ( m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1))
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f595])).

fof(f598,plain,
    ( spl5_6
    | spl5_62
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f593,f371,f595,f100])).

fof(f371,plain,
    ( spl5_36
  <=> k1_tarski(sK3(sK1)) = k6_domain_1(sK1,sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f593,plain,
    ( m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1))
    | v1_xboole_0(sK1)
    | ~ spl5_36 ),
    inference(superposition,[],[f176,f373])).

fof(f373,plain,
    ( k1_tarski(sK3(sK1)) = k6_domain_1(sK1,sK3(sK1))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f371])).

fof(f176,plain,(
    ! [X0] :
      ( m1_subset_1(k6_domain_1(X0,sK3(X0)),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | m1_subset_1(k6_domain_1(X0,sK3(X0)),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f68,f124])).

fof(f124,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f115,f61])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f62,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f374,plain,
    ( spl5_36
    | spl5_6 ),
    inference(avatar_split_clause,[],[f354,f100,f371])).

fof(f354,plain,
    ( k1_tarski(sK3(sK1)) = k6_domain_1(sK1,sK3(sK1))
    | spl5_6 ),
    inference(resolution,[],[f164,f102])).

fof(f102,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f164,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0)) ) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f67,f124])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f329,plain,
    ( spl5_31
    | spl5_23
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f312,f296,f229,f326])).

fof(f326,plain,
    ( spl5_31
  <=> k6_domain_1(u1_struct_0(sK0),sK3(sK1)) = k1_tarski(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f229,plain,
    ( spl5_23
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f296,plain,
    ( spl5_28
  <=> m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f312,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK3(sK1)) = k1_tarski(sK3(sK1))
    | ~ spl5_28 ),
    inference(resolution,[],[f298,f67])).

fof(f298,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f296])).

fof(f319,plain,
    ( spl5_29
    | spl5_4
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f310,f296,f85,f75,f90,f316])).

fof(f316,plain,
    ( spl5_29
  <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f310,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)
    | ~ spl5_28 ),
    inference(resolution,[],[f298,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f300,plain,
    ( ~ spl5_23
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f294,f280,f229])).

fof(f280,plain,
    ( spl5_27
  <=> r2_hidden(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f294,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_27 ),
    inference(resolution,[],[f282,f62])).

fof(f282,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f280])).

fof(f299,plain,
    ( spl5_28
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f293,f280,f296])).

fof(f293,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_27 ),
    inference(resolution,[],[f282,f115])).

fof(f283,plain,
    ( spl5_6
    | spl5_27
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f272,f135,f280,f100])).

fof(f135,plain,
    ( spl5_11
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f272,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ spl5_11 ),
    inference(resolution,[],[f158,f137])).

fof(f137,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(sK3(X0),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f69,f61])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f138,plain,
    ( spl5_11
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f132,f95,f135])).

fof(f132,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_5 ),
    inference(resolution,[],[f73,f97])).

fof(f113,plain,
    ( spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f41,f109,f105])).

fof(f41,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f112,plain,
    ( ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f42,f109,f105])).

fof(f42,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f103,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f43,f100])).

fof(f43,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f98,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f44,f95])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f93,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f45,f90])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f88,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f46,f85])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f83,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f47,f80])).

fof(f47,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f78,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f48,f75])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (13056)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (13074)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (13064)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (13074)Refutation not found, incomplete strategy% (13074)------------------------------
% 0.21/0.55  % (13074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (13067)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (13074)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (13074)Memory used [KB]: 10746
% 0.21/0.56  % (13074)Time elapsed: 0.139 s
% 0.21/0.56  % (13074)------------------------------
% 0.21/0.56  % (13074)------------------------------
% 0.21/0.56  % (13058)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (13076)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (13053)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (13070)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.58  % (13051)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.58  % (13057)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.58  % (13055)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (13060)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.58  % (13060)Refutation not found, incomplete strategy% (13060)------------------------------
% 0.21/0.58  % (13060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (13060)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (13060)Memory used [KB]: 10618
% 0.21/0.58  % (13060)Time elapsed: 0.179 s
% 0.21/0.58  % (13060)------------------------------
% 0.21/0.58  % (13060)------------------------------
% 0.21/0.58  % (13073)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.58  % (13067)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f798,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f112,f113,f138,f283,f299,f300,f319,f329,f374,f598,f608,f655,f674,f679,f684,f689,f694,f701,f706,f707,f795,f797])).
% 0.21/0.58  fof(f797,plain,(
% 0.21/0.58    spl5_96 | ~spl5_79),
% 0.21/0.58    inference(avatar_split_clause,[],[f796,f703,f792])).
% 0.21/0.58  fof(f792,plain,(
% 0.21/0.58    spl5_96 <=> l1_struct_0(sK2(sK0,sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).
% 0.21/0.58  fof(f703,plain,(
% 0.21/0.58    spl5_79 <=> l1_pre_topc(sK2(sK0,sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).
% 0.21/0.58  fof(f796,plain,(
% 0.21/0.58    l1_struct_0(sK2(sK0,sK1)) | ~spl5_79),
% 0.21/0.58    inference(resolution,[],[f705,f51])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.58  fof(f705,plain,(
% 0.21/0.58    l1_pre_topc(sK2(sK0,sK1)) | ~spl5_79),
% 0.21/0.58    inference(avatar_component_clause,[],[f703])).
% 0.21/0.58  fof(f795,plain,(
% 0.21/0.58    ~spl5_96 | spl5_8 | ~spl5_74 | ~spl5_78),
% 0.21/0.58    inference(avatar_split_clause,[],[f790,f698,f676,f109,f792])).
% 0.21/0.58  fof(f109,plain,(
% 0.21/0.58    spl5_8 <=> v1_zfmisc_1(sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.58  fof(f676,plain,(
% 0.21/0.58    spl5_74 <=> sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 0.21/0.58  fof(f698,plain,(
% 0.21/0.58    spl5_78 <=> v7_struct_0(sK2(sK0,sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).
% 0.21/0.58  fof(f790,plain,(
% 0.21/0.58    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | (~spl5_74 | ~spl5_78)),
% 0.21/0.58    inference(forward_demodulation,[],[f789,f678])).
% 0.21/0.58  fof(f678,plain,(
% 0.21/0.58    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl5_74),
% 0.21/0.58    inference(avatar_component_clause,[],[f676])).
% 0.21/0.58  fof(f789,plain,(
% 0.21/0.58    ~l1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1))) | ~spl5_78),
% 0.21/0.58    inference(resolution,[],[f700,f60])).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f34])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.21/0.58  fof(f700,plain,(
% 0.21/0.58    v7_struct_0(sK2(sK0,sK1)) | ~spl5_78),
% 0.21/0.58    inference(avatar_component_clause,[],[f698])).
% 0.21/0.58  fof(f707,plain,(
% 0.21/0.58    k6_domain_1(u1_struct_0(sK0),sK3(sK1)) != k1_tarski(sK3(sK1)) | sK1 != k1_tarski(sK3(sK1)) | v2_tex_2(sK1,sK0) | ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)),
% 0.21/0.58    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.58  fof(f706,plain,(
% 0.21/0.58    spl5_79 | ~spl5_1 | ~spl5_75),
% 0.21/0.58    inference(avatar_split_clause,[],[f696,f681,f75,f703])).
% 0.21/0.58  fof(f75,plain,(
% 0.21/0.58    spl5_1 <=> l1_pre_topc(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.58  fof(f681,plain,(
% 0.21/0.58    spl5_75 <=> m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).
% 0.21/0.58  fof(f696,plain,(
% 0.21/0.58    ~l1_pre_topc(sK0) | l1_pre_topc(sK2(sK0,sK1)) | ~spl5_75),
% 0.21/0.58    inference(resolution,[],[f683,f53])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.58  fof(f683,plain,(
% 0.21/0.58    m1_pre_topc(sK2(sK0,sK1),sK0) | ~spl5_75),
% 0.21/0.58    inference(avatar_component_clause,[],[f681])).
% 0.21/0.58  fof(f701,plain,(
% 0.21/0.58    ~spl5_76 | spl5_78 | spl5_77 | spl5_4 | ~spl5_1 | ~spl5_2 | ~spl5_75),
% 0.21/0.58    inference(avatar_split_clause,[],[f695,f681,f80,f75,f90,f691,f698,f686])).
% 0.21/0.58  fof(f686,plain,(
% 0.21/0.58    spl5_76 <=> v1_tdlat_3(sK2(sK0,sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 0.21/0.58  fof(f691,plain,(
% 0.21/0.58    spl5_77 <=> v2_struct_0(sK2(sK0,sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).
% 0.21/0.58  fof(f90,plain,(
% 0.21/0.58    spl5_4 <=> v2_struct_0(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.58  fof(f80,plain,(
% 0.21/0.58    spl5_2 <=> v2_tdlat_3(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.58  fof(f695,plain,(
% 0.21/0.58    ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~v1_tdlat_3(sK2(sK0,sK1)) | ~spl5_75),
% 0.21/0.58    inference(resolution,[],[f683,f114])).
% 0.21/0.58  fof(f114,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | v7_struct_0(X1) | ~v1_tdlat_3(X1)) )),
% 0.21/0.58    inference(global_subsumption,[],[f52,f54])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | v7_struct_0(X1) | ~v1_tdlat_3(X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f27])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    ( ! [X0] : (~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(flattening,[],[f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.21/0.58  fof(f694,plain,(
% 0.21/0.58    ~spl5_77 | ~spl5_7 | spl5_4 | spl5_6 | ~spl5_1 | ~spl5_3 | ~spl5_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f249,f95,f85,f75,f100,f90,f105,f691])).
% 0.21/0.58  fof(f105,plain,(
% 0.21/0.58    spl5_7 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.58  fof(f100,plain,(
% 0.21/0.58    spl5_6 <=> v1_xboole_0(sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.58  fof(f85,plain,(
% 0.21/0.58    spl5_3 <=> v2_pre_topc(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.58  fof(f95,plain,(
% 0.21/0.58    spl5_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.58  fof(f249,plain,(
% 0.21/0.58    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK2(sK0,sK1)) | ~spl5_5),
% 0.21/0.58    inference(resolution,[],[f56,f97])).
% 0.21/0.58  fof(f97,plain,(
% 0.21/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_5),
% 0.21/0.58    inference(avatar_component_clause,[],[f95])).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | ~v2_struct_0(sK2(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f18])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.21/0.58    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.58  fof(f14,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).
% 0.21/0.58  fof(f689,plain,(
% 0.21/0.58    spl5_76 | ~spl5_7 | spl5_4 | spl5_6 | ~spl5_1 | ~spl5_3 | ~spl5_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f259,f95,f85,f75,f100,f90,f105,f686])).
% 0.21/0.58  fof(f259,plain,(
% 0.21/0.58    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK2(sK0,sK1)) | ~spl5_5),
% 0.21/0.58    inference(resolution,[],[f57,f97])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | v1_tdlat_3(sK2(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f32])).
% 0.21/0.58  fof(f684,plain,(
% 0.21/0.58    spl5_75 | ~spl5_7 | spl5_4 | spl5_6 | ~spl5_1 | ~spl5_3 | ~spl5_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f267,f95,f85,f75,f100,f90,f105,f681])).
% 0.21/0.58  fof(f267,plain,(
% 0.21/0.58    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK2(sK0,sK1),sK0) | ~spl5_5),
% 0.21/0.58    inference(resolution,[],[f58,f97])).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | m1_pre_topc(sK2(X0,X1),X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f32])).
% 0.21/0.58  fof(f679,plain,(
% 0.21/0.58    spl5_74 | ~spl5_7 | spl5_4 | spl5_6 | ~spl5_1 | ~spl5_3 | ~spl5_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f285,f95,f85,f75,f100,f90,f105,f676])).
% 0.21/0.58  fof(f285,plain,(
% 0.21/0.58    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl5_5),
% 0.21/0.58    inference(resolution,[],[f59,f97])).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | u1_struct_0(sK2(X0,X1)) = X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f32])).
% 0.21/0.58  fof(f674,plain,(
% 0.21/0.58    spl5_73 | spl5_68 | ~spl5_8 | spl5_6 | ~spl5_63),
% 0.21/0.58    inference(avatar_split_clause,[],[f663,f605,f100,f109,f629,f671])).
% 0.21/0.58  fof(f671,plain,(
% 0.21/0.58    spl5_73 <=> sK1 = k1_tarski(sK3(sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 0.21/0.58  fof(f629,plain,(
% 0.21/0.58    spl5_68 <=> v1_xboole_0(k1_tarski(sK3(sK1)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 0.21/0.58  fof(f605,plain,(
% 0.21/0.58    spl5_63 <=> r1_tarski(k1_tarski(sK3(sK1)),sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 0.21/0.58  fof(f663,plain,(
% 0.21/0.58    v1_xboole_0(sK1) | ~v1_zfmisc_1(sK1) | v1_xboole_0(k1_tarski(sK3(sK1))) | sK1 = k1_tarski(sK3(sK1)) | ~spl5_63),
% 0.21/0.58    inference(resolution,[],[f607,f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | v1_xboole_0(X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X0) | X0 = X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.58    inference(flattening,[],[f21])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.58  fof(f607,plain,(
% 0.21/0.58    r1_tarski(k1_tarski(sK3(sK1)),sK1) | ~spl5_63),
% 0.21/0.58    inference(avatar_component_clause,[],[f605])).
% 0.21/0.58  fof(f655,plain,(
% 0.21/0.58    ~spl5_68),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f651])).
% 0.21/0.58  fof(f651,plain,(
% 0.21/0.58    $false | ~spl5_68),
% 0.21/0.58    inference(resolution,[],[f631,f49])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.58  fof(f631,plain,(
% 0.21/0.58    v1_xboole_0(k1_tarski(sK3(sK1))) | ~spl5_68),
% 0.21/0.58    inference(avatar_component_clause,[],[f629])).
% 0.21/0.58  fof(f608,plain,(
% 0.21/0.58    spl5_63 | ~spl5_62),
% 0.21/0.58    inference(avatar_split_clause,[],[f599,f595,f605])).
% 0.21/0.58  fof(f595,plain,(
% 0.21/0.58    spl5_62 <=> m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 0.21/0.58  fof(f599,plain,(
% 0.21/0.58    r1_tarski(k1_tarski(sK3(sK1)),sK1) | ~spl5_62),
% 0.21/0.58    inference(resolution,[],[f597,f73])).
% 0.21/0.58  fof(f73,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.58  fof(f597,plain,(
% 0.21/0.58    m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1)) | ~spl5_62),
% 0.21/0.58    inference(avatar_component_clause,[],[f595])).
% 0.21/0.58  fof(f598,plain,(
% 0.21/0.58    spl5_6 | spl5_62 | ~spl5_36),
% 0.21/0.58    inference(avatar_split_clause,[],[f593,f371,f595,f100])).
% 0.21/0.58  fof(f371,plain,(
% 0.21/0.58    spl5_36 <=> k1_tarski(sK3(sK1)) = k6_domain_1(sK1,sK3(sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.21/0.58  fof(f593,plain,(
% 0.21/0.58    m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1)) | v1_xboole_0(sK1) | ~spl5_36),
% 0.21/0.58    inference(superposition,[],[f176,f373])).
% 0.21/0.58  fof(f373,plain,(
% 0.21/0.58    k1_tarski(sK3(sK1)) = k6_domain_1(sK1,sK3(sK1)) | ~spl5_36),
% 0.21/0.58    inference(avatar_component_clause,[],[f371])).
% 0.21/0.58  fof(f176,plain,(
% 0.21/0.58    ( ! [X0] : (m1_subset_1(k6_domain_1(X0,sK3(X0)),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f174])).
% 0.21/0.58  fof(f174,plain,(
% 0.21/0.58    ( ! [X0] : (v1_xboole_0(X0) | m1_subset_1(k6_domain_1(X0,sK3(X0)),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.58    inference(resolution,[],[f68,f124])).
% 0.21/0.58  fof(f124,plain,(
% 0.21/0.58    ( ! [X0] : (m1_subset_1(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.58    inference(resolution,[],[f115,f61])).
% 0.21/0.58  fof(f61,plain,(
% 0.21/0.58    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.58  fof(f115,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.21/0.58    inference(global_subsumption,[],[f62,f65])).
% 0.21/0.58  fof(f65,plain,(
% 0.21/0.58    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.58  fof(f62,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f1])).
% 0.21/0.58  fof(f68,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f39])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.58    inference(flattening,[],[f38])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.58  fof(f374,plain,(
% 0.21/0.58    spl5_36 | spl5_6),
% 0.21/0.58    inference(avatar_split_clause,[],[f354,f100,f371])).
% 0.21/0.58  fof(f354,plain,(
% 0.21/0.58    k1_tarski(sK3(sK1)) = k6_domain_1(sK1,sK3(sK1)) | spl5_6),
% 0.21/0.58    inference(resolution,[],[f164,f102])).
% 0.21/0.58  fof(f102,plain,(
% 0.21/0.58    ~v1_xboole_0(sK1) | spl5_6),
% 0.21/0.58    inference(avatar_component_clause,[],[f100])).
% 0.21/0.58  fof(f164,plain,(
% 0.21/0.58    ( ! [X0] : (v1_xboole_0(X0) | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0))) )),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f162])).
% 0.21/0.58  fof(f162,plain,(
% 0.21/0.58    ( ! [X0] : (v1_xboole_0(X0) | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.58    inference(resolution,[],[f67,f124])).
% 0.21/0.58  fof(f67,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f37])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.58    inference(flattening,[],[f36])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.58  fof(f329,plain,(
% 0.21/0.58    spl5_31 | spl5_23 | ~spl5_28),
% 0.21/0.58    inference(avatar_split_clause,[],[f312,f296,f229,f326])).
% 0.21/0.58  fof(f326,plain,(
% 0.21/0.58    spl5_31 <=> k6_domain_1(u1_struct_0(sK0),sK3(sK1)) = k1_tarski(sK3(sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.21/0.58  fof(f229,plain,(
% 0.21/0.58    spl5_23 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.58  fof(f296,plain,(
% 0.21/0.58    spl5_28 <=> m1_subset_1(sK3(sK1),u1_struct_0(sK0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.58  fof(f312,plain,(
% 0.21/0.58    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK3(sK1)) = k1_tarski(sK3(sK1)) | ~spl5_28),
% 0.21/0.58    inference(resolution,[],[f298,f67])).
% 0.21/0.58  fof(f298,plain,(
% 0.21/0.58    m1_subset_1(sK3(sK1),u1_struct_0(sK0)) | ~spl5_28),
% 0.21/0.58    inference(avatar_component_clause,[],[f296])).
% 0.21/0.58  fof(f319,plain,(
% 0.21/0.58    spl5_29 | spl5_4 | ~spl5_1 | ~spl5_3 | ~spl5_28),
% 0.21/0.58    inference(avatar_split_clause,[],[f310,f296,f85,f75,f90,f316])).
% 0.21/0.58  fof(f316,plain,(
% 0.21/0.58    spl5_29 <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.21/0.58  fof(f310,plain,(
% 0.21/0.58    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0) | ~spl5_28),
% 0.21/0.58    inference(resolution,[],[f298,f55])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 0.21/0.58  fof(f300,plain,(
% 0.21/0.58    ~spl5_23 | ~spl5_27),
% 0.21/0.58    inference(avatar_split_clause,[],[f294,f280,f229])).
% 0.21/0.58  fof(f280,plain,(
% 0.21/0.58    spl5_27 <=> r2_hidden(sK3(sK1),u1_struct_0(sK0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.58  fof(f294,plain,(
% 0.21/0.58    ~v1_xboole_0(u1_struct_0(sK0)) | ~spl5_27),
% 0.21/0.58    inference(resolution,[],[f282,f62])).
% 0.21/0.58  fof(f282,plain,(
% 0.21/0.58    r2_hidden(sK3(sK1),u1_struct_0(sK0)) | ~spl5_27),
% 0.21/0.58    inference(avatar_component_clause,[],[f280])).
% 0.21/0.58  fof(f299,plain,(
% 0.21/0.58    spl5_28 | ~spl5_27),
% 0.21/0.58    inference(avatar_split_clause,[],[f293,f280,f296])).
% 0.21/0.58  fof(f293,plain,(
% 0.21/0.58    m1_subset_1(sK3(sK1),u1_struct_0(sK0)) | ~spl5_27),
% 0.21/0.58    inference(resolution,[],[f282,f115])).
% 0.21/0.58  fof(f283,plain,(
% 0.21/0.58    spl5_6 | spl5_27 | ~spl5_11),
% 0.21/0.58    inference(avatar_split_clause,[],[f272,f135,f280,f100])).
% 0.21/0.58  fof(f135,plain,(
% 0.21/0.58    spl5_11 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.58  fof(f272,plain,(
% 0.21/0.58    r2_hidden(sK3(sK1),u1_struct_0(sK0)) | v1_xboole_0(sK1) | ~spl5_11),
% 0.21/0.58    inference(resolution,[],[f158,f137])).
% 0.21/0.58  fof(f137,plain,(
% 0.21/0.58    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl5_11),
% 0.21/0.58    inference(avatar_component_clause,[],[f135])).
% 0.21/0.58  fof(f158,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(sK3(X0),X1) | v1_xboole_0(X0)) )),
% 0.21/0.58    inference(resolution,[],[f69,f61])).
% 0.21/0.58  fof(f69,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f40])).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.58  fof(f138,plain,(
% 0.21/0.58    spl5_11 | ~spl5_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f132,f95,f135])).
% 0.21/0.58  fof(f132,plain,(
% 0.21/0.58    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl5_5),
% 0.21/0.58    inference(resolution,[],[f73,f97])).
% 0.21/0.58  fof(f113,plain,(
% 0.21/0.58    spl5_7 | spl5_8),
% 0.21/0.58    inference(avatar_split_clause,[],[f41,f109,f105])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f20])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f19])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,negated_conjecture,(
% 0.21/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.58    inference(negated_conjecture,[],[f16])).
% 0.21/0.58  fof(f16,conjecture,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.58  fof(f112,plain,(
% 0.21/0.58    ~spl5_7 | ~spl5_8),
% 0.21/0.58    inference(avatar_split_clause,[],[f42,f109,f105])).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f20])).
% 0.21/0.58  fof(f103,plain,(
% 0.21/0.58    ~spl5_6),
% 0.21/0.58    inference(avatar_split_clause,[],[f43,f100])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    ~v1_xboole_0(sK1)),
% 0.21/0.58    inference(cnf_transformation,[],[f20])).
% 0.21/0.58  fof(f98,plain,(
% 0.21/0.58    spl5_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f44,f95])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    inference(cnf_transformation,[],[f20])).
% 0.21/0.58  fof(f93,plain,(
% 0.21/0.58    ~spl5_4),
% 0.21/0.58    inference(avatar_split_clause,[],[f45,f90])).
% 0.21/0.58  fof(f45,plain,(
% 0.21/0.58    ~v2_struct_0(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f20])).
% 0.21/0.58  fof(f88,plain,(
% 0.21/0.58    spl5_3),
% 0.21/0.58    inference(avatar_split_clause,[],[f46,f85])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    v2_pre_topc(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f20])).
% 0.21/0.58  fof(f83,plain,(
% 0.21/0.58    spl5_2),
% 0.21/0.58    inference(avatar_split_clause,[],[f47,f80])).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    v2_tdlat_3(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f20])).
% 0.21/0.58  fof(f78,plain,(
% 0.21/0.58    spl5_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f48,f75])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    l1_pre_topc(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f20])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (13067)------------------------------
% 0.21/0.58  % (13067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (13067)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (13067)Memory used [KB]: 11257
% 0.21/0.58  % (13067)Time elapsed: 0.129 s
% 0.21/0.58  % (13067)------------------------------
% 0.21/0.58  % (13067)------------------------------
% 0.21/0.59  % (13063)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.59  % (13075)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.59  % (13052)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.59  % (13078)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.59  % (13081)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.59  % (13065)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.59  % (13069)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.60  % (13071)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.60  % (13072)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.60  % (13061)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.60  % (13061)Refutation not found, incomplete strategy% (13061)------------------------------
% 0.21/0.60  % (13061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (13061)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (13061)Memory used [KB]: 10618
% 0.21/0.60  % (13061)Time elapsed: 0.183 s
% 0.21/0.60  % (13061)------------------------------
% 0.21/0.60  % (13061)------------------------------
% 1.84/0.60  % (13077)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.84/0.60  % (13062)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.84/0.60  % (13079)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.84/0.61  % (13059)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.84/0.61  % (13042)Success in time 0.247 s
%------------------------------------------------------------------------------
