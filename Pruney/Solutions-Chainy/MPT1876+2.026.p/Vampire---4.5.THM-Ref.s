%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 331 expanded)
%              Number of leaves         :   47 ( 154 expanded)
%              Depth                    :    8
%              Number of atoms          :  639 (1264 expanded)
%              Number of equality atoms :   35 (  65 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (20003)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f756,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f115,f116,f138,f181,f195,f218,f229,f364,f432,f572,f580,f591,f592,f597,f602,f607,f612,f622,f626,f643,f648,f658,f754,f755])).

fof(f755,plain,
    ( sK1 != u1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | ~ v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f754,plain,
    ( spl5_94
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f739,f645,f655])).

fof(f655,plain,
    ( spl5_94
  <=> l1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

% (20000)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f645,plain,
    ( spl5_92
  <=> l1_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f739,plain,
    ( l1_struct_0(sK2(sK0,sK1))
    | ~ spl5_92 ),
    inference(resolution,[],[f647,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f647,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl5_92 ),
    inference(avatar_component_clause,[],[f645])).

fof(f658,plain,
    ( spl5_93
    | ~ spl5_94
    | ~ spl5_91 ),
    inference(avatar_split_clause,[],[f649,f640,f655,f651])).

fof(f651,plain,
    ( spl5_93
  <=> v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f640,plain,
    ( spl5_91
  <=> v7_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f649,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl5_91 ),
    inference(resolution,[],[f642,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f642,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ spl5_91 ),
    inference(avatar_component_clause,[],[f640])).

fof(f648,plain,
    ( spl5_92
    | ~ spl5_1
    | ~ spl5_85 ),
    inference(avatar_split_clause,[],[f634,f599,f78,f645])).

fof(f78,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f599,plain,
    ( spl5_85
  <=> m1_pre_topc(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f634,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2(sK0,sK1))
    | ~ spl5_85 ),
    inference(resolution,[],[f601,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f601,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl5_85 ),
    inference(avatar_component_clause,[],[f599])).

fof(f643,plain,
    ( ~ spl5_86
    | spl5_91
    | spl5_87
    | spl5_4
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_85 ),
    inference(avatar_split_clause,[],[f633,f599,f83,f78,f93,f609,f640,f604])).

fof(f604,plain,
    ( spl5_86
  <=> v1_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f609,plain,
    ( spl5_87
  <=> v2_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f93,plain,
    ( spl5_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f83,plain,
    ( spl5_2
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f633,plain,
    ( ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl5_85 ),
    inference(resolution,[],[f601,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | v7_struct_0(X1)
      | ~ v1_tdlat_3(X1) ) ),
    inference(global_subsumption,[],[f59,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | v7_struct_0(X1)
      | ~ v1_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f59,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

% (20005)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f27,plain,(
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

fof(f626,plain,(
    ~ spl5_58 ),
    inference(avatar_contradiction_clause,[],[f624])).

fof(f624,plain,
    ( $false
    | ~ spl5_58 ),
    inference(resolution,[],[f431,f56])).

fof(f56,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f431,plain,
    ( v1_xboole_0(k1_tarski(sK4(sK1)))
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f429])).

fof(f429,plain,
    ( spl5_58
  <=> v1_xboole_0(k1_tarski(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f622,plain,
    ( spl5_6
    | spl5_52
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f620,f361,f396,f103])).

fof(f103,plain,
    ( spl5_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f396,plain,
    ( spl5_52
  <=> r1_tarski(k1_tarski(sK4(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f361,plain,
    ( spl5_46
  <=> k6_domain_1(sK1,sK4(sK1)) = k1_tarski(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f620,plain,
    ( r1_tarski(k1_tarski(sK4(sK1)),sK1)
    | v1_xboole_0(sK1)
    | ~ spl5_46 ),
    inference(superposition,[],[f265,f363])).

fof(f363,plain,
    ( k6_domain_1(sK1,sK4(sK1)) = k1_tarski(sK4(sK1))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f361])).

fof(f265,plain,(
    ! [X1] :
      ( r1_tarski(k6_domain_1(X1,sK4(X1)),X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f150,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f150,plain,(
    ! [X0] :
      ( m1_subset_1(k6_domain_1(X0,sK4(X0)),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f75,f73])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f612,plain,
    ( ~ spl5_87
    | ~ spl5_7
    | spl5_4
    | spl5_6
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f255,f98,f88,f78,f103,f93,f108,f609])).

fof(f108,plain,
    ( spl5_7
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f88,plain,
    ( spl5_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f98,plain,
    ( spl5_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f255,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl5_5 ),
    inference(resolution,[],[f64,f100])).

fof(f100,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v2_struct_0(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
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

fof(f607,plain,
    ( spl5_86
    | ~ spl5_7
    | spl5_4
    | spl5_6
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f262,f98,f88,f78,f103,f93,f108,f604])).

fof(f262,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl5_5 ),
    inference(resolution,[],[f65,f100])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | v1_tdlat_3(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f602,plain,
    ( spl5_85
    | ~ spl5_7
    | spl5_4
    | spl5_6
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f274,f98,f88,f78,f103,f93,f108,f599])).

fof(f274,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f66,f100])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f597,plain,
    ( spl5_84
    | ~ spl5_7
    | spl5_4
    | spl5_6
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f280,f98,f88,f78,f103,f93,f108,f594])).

fof(f594,plain,
    ( spl5_84
  <=> sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f280,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl5_5 ),
    inference(resolution,[],[f67,f100])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f592,plain,
    ( sK1 != k6_domain_1(u1_struct_0(sK0),sK4(sK1))
    | v2_tex_2(sK1,sK0)
    | ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK4(sK1)),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f591,plain,
    ( spl5_11
    | spl5_83
    | ~ spl5_57
    | ~ spl5_80 ),
    inference(avatar_split_clause,[],[f586,f569,f425,f588,f135])).

fof(f135,plain,
    ( spl5_11
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f588,plain,
    ( spl5_83
  <=> sK1 = k6_domain_1(u1_struct_0(sK0),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f425,plain,
    ( spl5_57
  <=> sK1 = k1_tarski(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f569,plain,
    ( spl5_80
  <=> m1_subset_1(sK4(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f586,plain,
    ( sK1 = k6_domain_1(u1_struct_0(sK0),sK4(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_57
    | ~ spl5_80 ),
    inference(forward_demodulation,[],[f575,f427])).

fof(f427,plain,
    ( sK1 = k1_tarski(sK4(sK1))
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f425])).

fof(f575,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_tarski(sK4(sK1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK1))
    | ~ spl5_80 ),
    inference(resolution,[],[f571,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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

fof(f571,plain,
    ( m1_subset_1(sK4(sK1),u1_struct_0(sK0))
    | ~ spl5_80 ),
    inference(avatar_component_clause,[],[f569])).

fof(f580,plain,
    ( spl5_81
    | spl5_4
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_80 ),
    inference(avatar_split_clause,[],[f573,f569,f88,f78,f93,f577])).

fof(f577,plain,
    ( spl5_81
  <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK4(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f573,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK4(sK1)),sK0)
    | ~ spl5_80 ),
    inference(resolution,[],[f571,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f572,plain,
    ( spl5_80
    | ~ spl5_24
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f567,f227,f215,f569])).

fof(f215,plain,
    ( spl5_24
  <=> sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f227,plain,
    ( spl5_26
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3(sK0,sK1)))
        | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f567,plain,
    ( m1_subset_1(sK4(sK1),u1_struct_0(sK0))
    | ~ spl5_24
    | ~ spl5_26 ),
    inference(resolution,[],[f566,f73])).

fof(f566,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_24
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f228,f217])).

fof(f217,plain,
    ( sK1 = u1_struct_0(sK3(sK0,sK1))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f215])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3(sK0,sK1)))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f227])).

fof(f432,plain,
    ( spl5_57
    | spl5_58
    | ~ spl5_8
    | spl5_6
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f423,f396,f103,f112,f429,f425])).

fof(f112,plain,
    ( spl5_8
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f423,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(k1_tarski(sK4(sK1)))
    | sK1 = k1_tarski(sK4(sK1))
    | ~ spl5_52 ),
    inference(resolution,[],[f398,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f398,plain,
    ( r1_tarski(k1_tarski(sK4(sK1)),sK1)
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f396])).

fof(f364,plain,
    ( spl5_46
    | spl5_6 ),
    inference(avatar_split_clause,[],[f354,f103,f361])).

fof(f354,plain,
    ( k6_domain_1(sK1,sK4(sK1)) = k1_tarski(sK4(sK1))
    | spl5_6 ),
    inference(resolution,[],[f139,f105])).

fof(f105,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f139,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK4(X0)) = k1_tarski(sK4(X0)) ) ),
    inference(resolution,[],[f74,f73])).

fof(f229,plain,
    ( spl5_26
    | spl5_4
    | spl5_18
    | ~ spl5_1
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f225,f192,f78,f178,f93,f227])).

fof(f178,plain,
    ( spl5_18
  <=> v2_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f192,plain,
    ( spl5_20
  <=> m1_pre_topc(sK3(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK3(sK0,sK1))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3(sK0,sK1)))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_20 ),
    inference(resolution,[],[f71,f194])).

fof(f194,plain,
    ( m1_pre_topc(sK3(sK0,sK1),sK0)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f192])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f218,plain,
    ( spl5_24
    | spl5_4
    | spl5_6
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f213,f98,f78,f103,f93,f215])).

fof(f213,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1))
    | ~ spl5_5 ),
    inference(resolution,[],[f70,f100])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | u1_struct_0(sK3(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
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

fof(f195,plain,
    ( spl5_20
    | spl5_4
    | spl5_6
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f190,f98,f78,f103,f93,f192])).

fof(f190,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK3(sK0,sK1),sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f69,f100])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | m1_pre_topc(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f181,plain,
    ( ~ spl5_18
    | spl5_4
    | spl5_6
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f176,f98,f78,f103,f93,f178])).

fof(f176,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(sK3(sK0,sK1))
    | ~ spl5_5 ),
    inference(resolution,[],[f68,f100])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_struct_0(sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f138,plain,
    ( spl5_6
    | ~ spl5_11
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f133,f98,f135,f103])).

fof(f133,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f61,f100])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f116,plain,
    ( spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f48,f112,f108])).

fof(f48,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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
    ( ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f49,f112,f108])).

fof(f49,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f106,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f50,f103])).

fof(f50,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f101,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f51,f98])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f96,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f52,f93])).

% (20011)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f91,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f53,f88])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f86,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f54,f83])).

fof(f54,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f81,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f55,f78])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:46:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (20020)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (20014)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (20006)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (20012)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (20016)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (20029)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (20024)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (20010)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (20008)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (20010)Refutation not found, incomplete strategy% (20010)------------------------------
% 0.22/0.55  % (20010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20010)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20010)Memory used [KB]: 10618
% 0.22/0.55  % (20010)Time elapsed: 0.127 s
% 0.22/0.55  % (20010)------------------------------
% 0.22/0.55  % (20010)------------------------------
% 0.22/0.55  % (20022)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (20002)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (20016)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  % (20003)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  fof(f756,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f115,f116,f138,f181,f195,f218,f229,f364,f432,f572,f580,f591,f592,f597,f602,f607,f612,f622,f626,f643,f648,f658,f754,f755])).
% 0.22/0.56  fof(f755,plain,(
% 0.22/0.56    sK1 != u1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | ~v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1)))),
% 0.22/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.56  fof(f754,plain,(
% 0.22/0.56    spl5_94 | ~spl5_92),
% 0.22/0.56    inference(avatar_split_clause,[],[f739,f645,f655])).
% 0.22/0.56  fof(f655,plain,(
% 0.22/0.56    spl5_94 <=> l1_struct_0(sK2(sK0,sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).
% 0.22/0.56  % (20000)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.56  fof(f645,plain,(
% 0.22/0.56    spl5_92 <=> l1_pre_topc(sK2(sK0,sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).
% 0.22/0.56  fof(f739,plain,(
% 0.22/0.56    l1_struct_0(sK2(sK0,sK1)) | ~spl5_92),
% 0.22/0.56    inference(resolution,[],[f647,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.56  fof(f647,plain,(
% 0.22/0.56    l1_pre_topc(sK2(sK0,sK1)) | ~spl5_92),
% 0.22/0.56    inference(avatar_component_clause,[],[f645])).
% 0.22/0.56  fof(f658,plain,(
% 0.22/0.56    spl5_93 | ~spl5_94 | ~spl5_91),
% 0.22/0.56    inference(avatar_split_clause,[],[f649,f640,f655,f651])).
% 0.22/0.56  fof(f651,plain,(
% 0.22/0.56    spl5_93 <=> v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).
% 0.22/0.56  fof(f640,plain,(
% 0.22/0.56    spl5_91 <=> v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).
% 0.22/0.56  fof(f649,plain,(
% 0.22/0.56    ~l1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1))) | ~spl5_91),
% 0.22/0.56    inference(resolution,[],[f642,f72])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.22/0.56  fof(f642,plain,(
% 0.22/0.56    v7_struct_0(sK2(sK0,sK1)) | ~spl5_91),
% 0.22/0.56    inference(avatar_component_clause,[],[f640])).
% 0.22/0.56  fof(f648,plain,(
% 0.22/0.56    spl5_92 | ~spl5_1 | ~spl5_85),
% 0.22/0.56    inference(avatar_split_clause,[],[f634,f599,f78,f645])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    spl5_1 <=> l1_pre_topc(sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.56  fof(f599,plain,(
% 0.22/0.56    spl5_85 <=> m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).
% 0.22/0.56  fof(f634,plain,(
% 0.22/0.56    ~l1_pre_topc(sK0) | l1_pre_topc(sK2(sK0,sK1)) | ~spl5_85),
% 0.22/0.56    inference(resolution,[],[f601,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.57  fof(f601,plain,(
% 0.22/0.57    m1_pre_topc(sK2(sK0,sK1),sK0) | ~spl5_85),
% 0.22/0.57    inference(avatar_component_clause,[],[f599])).
% 0.22/0.57  fof(f643,plain,(
% 0.22/0.57    ~spl5_86 | spl5_91 | spl5_87 | spl5_4 | ~spl5_1 | ~spl5_2 | ~spl5_85),
% 0.22/0.57    inference(avatar_split_clause,[],[f633,f599,f83,f78,f93,f609,f640,f604])).
% 0.22/0.57  fof(f604,plain,(
% 0.22/0.57    spl5_86 <=> v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).
% 0.22/0.57  fof(f609,plain,(
% 0.22/0.57    spl5_87 <=> v2_struct_0(sK2(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 0.22/0.57  fof(f93,plain,(
% 0.22/0.57    spl5_4 <=> v2_struct_0(sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.57  fof(f83,plain,(
% 0.22/0.57    spl5_2 <=> v2_tdlat_3(sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.57  fof(f633,plain,(
% 0.22/0.57    ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~v1_tdlat_3(sK2(sK0,sK1)) | ~spl5_85),
% 0.22/0.57    inference(resolution,[],[f601,f117])).
% 0.22/0.57  fof(f117,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | v7_struct_0(X1) | ~v1_tdlat_3(X1)) )),
% 0.22/0.57    inference(global_subsumption,[],[f59,f62])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | v7_struct_0(X1) | ~v1_tdlat_3(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,axiom,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    ( ! [X0] : (~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(flattening,[],[f27])).
% 0.22/0.57  % (20005)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.22/0.57  fof(f626,plain,(
% 0.22/0.57    ~spl5_58),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f624])).
% 0.22/0.57  fof(f624,plain,(
% 0.22/0.57    $false | ~spl5_58),
% 0.22/0.57    inference(resolution,[],[f431,f56])).
% 0.22/0.57  fof(f56,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.22/0.57  fof(f431,plain,(
% 0.22/0.57    v1_xboole_0(k1_tarski(sK4(sK1))) | ~spl5_58),
% 0.22/0.57    inference(avatar_component_clause,[],[f429])).
% 0.22/0.57  fof(f429,plain,(
% 0.22/0.57    spl5_58 <=> v1_xboole_0(k1_tarski(sK4(sK1)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 0.22/0.57  fof(f622,plain,(
% 0.22/0.57    spl5_6 | spl5_52 | ~spl5_46),
% 0.22/0.57    inference(avatar_split_clause,[],[f620,f361,f396,f103])).
% 0.22/0.57  fof(f103,plain,(
% 0.22/0.57    spl5_6 <=> v1_xboole_0(sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.57  fof(f396,plain,(
% 0.22/0.57    spl5_52 <=> r1_tarski(k1_tarski(sK4(sK1)),sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 0.22/0.57  fof(f361,plain,(
% 0.22/0.57    spl5_46 <=> k6_domain_1(sK1,sK4(sK1)) = k1_tarski(sK4(sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 0.22/0.57  fof(f620,plain,(
% 0.22/0.57    r1_tarski(k1_tarski(sK4(sK1)),sK1) | v1_xboole_0(sK1) | ~spl5_46),
% 0.22/0.57    inference(superposition,[],[f265,f363])).
% 0.22/0.57  fof(f363,plain,(
% 0.22/0.57    k6_domain_1(sK1,sK4(sK1)) = k1_tarski(sK4(sK1)) | ~spl5_46),
% 0.22/0.57    inference(avatar_component_clause,[],[f361])).
% 0.22/0.57  fof(f265,plain,(
% 0.22/0.57    ( ! [X1] : (r1_tarski(k6_domain_1(X1,sK4(X1)),X1) | v1_xboole_0(X1)) )),
% 0.22/0.57    inference(resolution,[],[f150,f76])).
% 0.22/0.57  fof(f76,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.57    inference(unused_predicate_definition_removal,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.57  fof(f150,plain,(
% 0.22/0.57    ( ! [X0] : (m1_subset_1(k6_domain_1(X0,sK4(X0)),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.57    inference(resolution,[],[f75,f73])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.22/0.57  fof(f75,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f46])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.57    inference(flattening,[],[f45])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.22/0.57  fof(f612,plain,(
% 0.22/0.57    ~spl5_87 | ~spl5_7 | spl5_4 | spl5_6 | ~spl5_1 | ~spl5_3 | ~spl5_5),
% 0.22/0.57    inference(avatar_split_clause,[],[f255,f98,f88,f78,f103,f93,f108,f609])).
% 0.22/0.57  fof(f108,plain,(
% 0.22/0.57    spl5_7 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.57  fof(f88,plain,(
% 0.22/0.57    spl5_3 <=> v2_pre_topc(sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.57  fof(f98,plain,(
% 0.22/0.57    spl5_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.57  fof(f255,plain,(
% 0.22/0.57    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK2(sK0,sK1)) | ~spl5_5),
% 0.22/0.57    inference(resolution,[],[f64,f100])).
% 0.22/0.57  fof(f100,plain,(
% 0.22/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_5),
% 0.22/0.57    inference(avatar_component_clause,[],[f98])).
% 0.22/0.57  fof(f64,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | ~v2_struct_0(sK2(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.22/0.57    inference(pure_predicate_removal,[],[f15])).
% 0.22/0.57  fof(f15,axiom,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).
% 0.22/0.57  fof(f607,plain,(
% 0.22/0.57    spl5_86 | ~spl5_7 | spl5_4 | spl5_6 | ~spl5_1 | ~spl5_3 | ~spl5_5),
% 0.22/0.57    inference(avatar_split_clause,[],[f262,f98,f88,f78,f103,f93,f108,f604])).
% 0.22/0.57  fof(f262,plain,(
% 0.22/0.57    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK2(sK0,sK1)) | ~spl5_5),
% 0.22/0.57    inference(resolution,[],[f65,f100])).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | v1_tdlat_3(sK2(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f36])).
% 0.22/0.57  fof(f602,plain,(
% 0.22/0.57    spl5_85 | ~spl5_7 | spl5_4 | spl5_6 | ~spl5_1 | ~spl5_3 | ~spl5_5),
% 0.22/0.57    inference(avatar_split_clause,[],[f274,f98,f88,f78,f103,f93,f108,f599])).
% 0.22/0.57  fof(f274,plain,(
% 0.22/0.57    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK2(sK0,sK1),sK0) | ~spl5_5),
% 0.22/0.57    inference(resolution,[],[f66,f100])).
% 0.22/0.57  fof(f66,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | m1_pre_topc(sK2(X0,X1),X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f36])).
% 0.22/0.57  fof(f597,plain,(
% 0.22/0.57    spl5_84 | ~spl5_7 | spl5_4 | spl5_6 | ~spl5_1 | ~spl5_3 | ~spl5_5),
% 0.22/0.57    inference(avatar_split_clause,[],[f280,f98,f88,f78,f103,f93,f108,f594])).
% 0.22/0.57  fof(f594,plain,(
% 0.22/0.57    spl5_84 <=> sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).
% 0.22/0.57  fof(f280,plain,(
% 0.22/0.57    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl5_5),
% 0.22/0.57    inference(resolution,[],[f67,f100])).
% 0.22/0.57  fof(f67,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | u1_struct_0(sK2(X0,X1)) = X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f36])).
% 0.22/0.57  fof(f592,plain,(
% 0.22/0.57    sK1 != k6_domain_1(u1_struct_0(sK0),sK4(sK1)) | v2_tex_2(sK1,sK0) | ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK4(sK1)),sK0)),
% 0.22/0.57    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.57  fof(f591,plain,(
% 0.22/0.57    spl5_11 | spl5_83 | ~spl5_57 | ~spl5_80),
% 0.22/0.57    inference(avatar_split_clause,[],[f586,f569,f425,f588,f135])).
% 0.22/0.57  fof(f135,plain,(
% 0.22/0.57    spl5_11 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.57  fof(f588,plain,(
% 0.22/0.57    spl5_83 <=> sK1 = k6_domain_1(u1_struct_0(sK0),sK4(sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).
% 0.22/0.57  fof(f425,plain,(
% 0.22/0.57    spl5_57 <=> sK1 = k1_tarski(sK4(sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 0.22/0.57  fof(f569,plain,(
% 0.22/0.57    spl5_80 <=> m1_subset_1(sK4(sK1),u1_struct_0(sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).
% 0.22/0.57  fof(f586,plain,(
% 0.22/0.57    sK1 = k6_domain_1(u1_struct_0(sK0),sK4(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl5_57 | ~spl5_80)),
% 0.22/0.57    inference(forward_demodulation,[],[f575,f427])).
% 0.22/0.57  fof(f427,plain,(
% 0.22/0.57    sK1 = k1_tarski(sK4(sK1)) | ~spl5_57),
% 0.22/0.57    inference(avatar_component_clause,[],[f425])).
% 0.22/0.57  fof(f575,plain,(
% 0.22/0.57    v1_xboole_0(u1_struct_0(sK0)) | k1_tarski(sK4(sK1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK1)) | ~spl5_80),
% 0.22/0.57    inference(resolution,[],[f571,f74])).
% 0.22/0.57  fof(f74,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f44])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.57    inference(flattening,[],[f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.57  fof(f571,plain,(
% 0.22/0.57    m1_subset_1(sK4(sK1),u1_struct_0(sK0)) | ~spl5_80),
% 0.22/0.57    inference(avatar_component_clause,[],[f569])).
% 0.22/0.57  fof(f580,plain,(
% 0.22/0.57    spl5_81 | spl5_4 | ~spl5_1 | ~spl5_3 | ~spl5_80),
% 0.22/0.57    inference(avatar_split_clause,[],[f573,f569,f88,f78,f93,f577])).
% 0.22/0.57  fof(f577,plain,(
% 0.22/0.57    spl5_81 <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK4(sK1)),sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).
% 0.22/0.57  fof(f573,plain,(
% 0.22/0.57    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK4(sK1)),sK0) | ~spl5_80),
% 0.22/0.57    inference(resolution,[],[f571,f63])).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,axiom,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 0.22/0.57  fof(f572,plain,(
% 0.22/0.57    spl5_80 | ~spl5_24 | ~spl5_26),
% 0.22/0.57    inference(avatar_split_clause,[],[f567,f227,f215,f569])).
% 0.22/0.57  fof(f215,plain,(
% 0.22/0.57    spl5_24 <=> sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.57  fof(f227,plain,(
% 0.22/0.57    spl5_26 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3(sK0,sK1))) | m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.22/0.57  fof(f567,plain,(
% 0.22/0.57    m1_subset_1(sK4(sK1),u1_struct_0(sK0)) | (~spl5_24 | ~spl5_26)),
% 0.22/0.57    inference(resolution,[],[f566,f73])).
% 0.22/0.57  fof(f566,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_subset_1(X0,sK1) | m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl5_24 | ~spl5_26)),
% 0.22/0.57    inference(forward_demodulation,[],[f228,f217])).
% 0.22/0.57  fof(f217,plain,(
% 0.22/0.57    sK1 = u1_struct_0(sK3(sK0,sK1)) | ~spl5_24),
% 0.22/0.57    inference(avatar_component_clause,[],[f215])).
% 0.22/0.57  fof(f228,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3(sK0,sK1))) | m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl5_26),
% 0.22/0.57    inference(avatar_component_clause,[],[f227])).
% 0.22/0.57  fof(f432,plain,(
% 0.22/0.57    spl5_57 | spl5_58 | ~spl5_8 | spl5_6 | ~spl5_52),
% 0.22/0.57    inference(avatar_split_clause,[],[f423,f396,f103,f112,f429,f425])).
% 0.22/0.57  fof(f112,plain,(
% 0.22/0.57    spl5_8 <=> v1_zfmisc_1(sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.57  fof(f423,plain,(
% 0.22/0.57    v1_xboole_0(sK1) | ~v1_zfmisc_1(sK1) | v1_xboole_0(k1_tarski(sK4(sK1))) | sK1 = k1_tarski(sK4(sK1)) | ~spl5_52),
% 0.22/0.57    inference(resolution,[],[f398,f57])).
% 0.22/0.57  fof(f57,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | v1_xboole_0(X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X0) | X0 = X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.57    inference(flattening,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,axiom,(
% 0.22/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.22/0.57  fof(f398,plain,(
% 0.22/0.57    r1_tarski(k1_tarski(sK4(sK1)),sK1) | ~spl5_52),
% 0.22/0.57    inference(avatar_component_clause,[],[f396])).
% 0.22/0.57  fof(f364,plain,(
% 0.22/0.57    spl5_46 | spl5_6),
% 0.22/0.57    inference(avatar_split_clause,[],[f354,f103,f361])).
% 0.22/0.57  fof(f354,plain,(
% 0.22/0.57    k6_domain_1(sK1,sK4(sK1)) = k1_tarski(sK4(sK1)) | spl5_6),
% 0.22/0.57    inference(resolution,[],[f139,f105])).
% 0.22/0.57  fof(f105,plain,(
% 0.22/0.57    ~v1_xboole_0(sK1) | spl5_6),
% 0.22/0.57    inference(avatar_component_clause,[],[f103])).
% 0.22/0.57  fof(f139,plain,(
% 0.22/0.57    ( ! [X0] : (v1_xboole_0(X0) | k6_domain_1(X0,sK4(X0)) = k1_tarski(sK4(X0))) )),
% 0.22/0.57    inference(resolution,[],[f74,f73])).
% 0.22/0.57  fof(f229,plain,(
% 0.22/0.57    spl5_26 | spl5_4 | spl5_18 | ~spl5_1 | ~spl5_20),
% 0.22/0.57    inference(avatar_split_clause,[],[f225,f192,f78,f178,f93,f227])).
% 0.22/0.57  fof(f178,plain,(
% 0.22/0.57    spl5_18 <=> v2_struct_0(sK3(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.57  fof(f192,plain,(
% 0.22/0.57    spl5_20 <=> m1_pre_topc(sK3(sK0,sK1),sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.22/0.57  fof(f225,plain,(
% 0.22/0.57    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK3(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK3(sK0,sK1))) | m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl5_20),
% 0.22/0.57    inference(resolution,[],[f71,f194])).
% 0.22/0.57  fof(f194,plain,(
% 0.22/0.57    m1_pre_topc(sK3(sK0,sK1),sK0) | ~spl5_20),
% 0.22/0.57    inference(avatar_component_clause,[],[f192])).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f40])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.22/0.57  fof(f218,plain,(
% 0.22/0.57    spl5_24 | spl5_4 | spl5_6 | ~spl5_1 | ~spl5_5),
% 0.22/0.57    inference(avatar_split_clause,[],[f213,f98,f78,f103,f93,f215])).
% 0.22/0.57  fof(f213,plain,(
% 0.22/0.57    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | sK1 = u1_struct_0(sK3(sK0,sK1)) | ~spl5_5),
% 0.22/0.57    inference(resolution,[],[f70,f100])).
% 0.22/0.57  fof(f70,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | u1_struct_0(sK3(X0,X1)) = X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f37])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 0.22/0.57    inference(pure_predicate_removal,[],[f13])).
% 0.22/0.57  fof(f13,axiom,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.22/0.57  fof(f195,plain,(
% 0.22/0.57    spl5_20 | spl5_4 | spl5_6 | ~spl5_1 | ~spl5_5),
% 0.22/0.57    inference(avatar_split_clause,[],[f190,f98,f78,f103,f93,f192])).
% 0.22/0.57  fof(f190,plain,(
% 0.22/0.57    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | m1_pre_topc(sK3(sK0,sK1),sK0) | ~spl5_5),
% 0.22/0.57    inference(resolution,[],[f69,f100])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | m1_pre_topc(sK3(X0,X1),X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f38])).
% 0.22/0.57  fof(f181,plain,(
% 0.22/0.57    ~spl5_18 | spl5_4 | spl5_6 | ~spl5_1 | ~spl5_5),
% 0.22/0.57    inference(avatar_split_clause,[],[f176,f98,f78,f103,f93,f178])).
% 0.22/0.57  fof(f176,plain,(
% 0.22/0.57    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_struct_0(sK3(sK0,sK1)) | ~spl5_5),
% 0.22/0.57    inference(resolution,[],[f68,f100])).
% 0.22/0.57  fof(f68,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_struct_0(sK3(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f38])).
% 0.22/0.57  fof(f138,plain,(
% 0.22/0.57    spl5_6 | ~spl5_11 | ~spl5_5),
% 0.22/0.57    inference(avatar_split_clause,[],[f133,f98,f135,f103])).
% 0.22/0.57  fof(f133,plain,(
% 0.22/0.57    ~v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(sK1) | ~spl5_5),
% 0.22/0.57    inference(resolution,[],[f61,f100])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.57  fof(f116,plain,(
% 0.22/0.57    spl5_7 | spl5_8),
% 0.22/0.57    inference(avatar_split_clause,[],[f48,f112,f108])).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,negated_conjecture,(
% 0.22/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.57    inference(negated_conjecture,[],[f17])).
% 0.22/0.57  fof(f17,conjecture,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.22/0.57  fof(f115,plain,(
% 0.22/0.57    ~spl5_7 | ~spl5_8),
% 0.22/0.57    inference(avatar_split_clause,[],[f49,f112,f108])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f106,plain,(
% 0.22/0.57    ~spl5_6),
% 0.22/0.57    inference(avatar_split_clause,[],[f50,f103])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    ~v1_xboole_0(sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f101,plain,(
% 0.22/0.57    spl5_5),
% 0.22/0.57    inference(avatar_split_clause,[],[f51,f98])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f96,plain,(
% 0.22/0.57    ~spl5_4),
% 0.22/0.57    inference(avatar_split_clause,[],[f52,f93])).
% 0.22/0.57  % (20011)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    ~v2_struct_0(sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f91,plain,(
% 0.22/0.57    spl5_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f53,f88])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    v2_pre_topc(sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f86,plain,(
% 0.22/0.57    spl5_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f54,f83])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    v2_tdlat_3(sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f81,plain,(
% 0.22/0.57    spl5_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f55,f78])).
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    l1_pre_topc(sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (20016)------------------------------
% 0.22/0.57  % (20016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (20016)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (20016)Memory used [KB]: 11257
% 0.22/0.57  % (20016)Time elapsed: 0.107 s
% 0.22/0.57  % (20016)------------------------------
% 0.22/0.57  % (20016)------------------------------
% 0.22/0.57  % (20026)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.57  % (19999)Success in time 0.203 s
%------------------------------------------------------------------------------
