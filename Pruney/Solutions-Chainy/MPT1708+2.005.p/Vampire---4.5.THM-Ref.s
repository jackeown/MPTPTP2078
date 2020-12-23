%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:48 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 312 expanded)
%              Number of leaves         :   37 ( 125 expanded)
%              Depth                    :   10
%              Number of atoms          :  537 (1423 expanded)
%              Number of equality atoms :   34 ( 139 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (19106)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f2653,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f103,f108,f113,f118,f127,f170,f225,f244,f250,f298,f411,f448,f457,f470,f1258,f2494,f2513,f2587,f2636,f2649,f2652])).

fof(f2652,plain,
    ( spl6_9
    | ~ spl6_218 ),
    inference(avatar_split_clause,[],[f2651,f2633,f120])).

fof(f120,plain,
    ( spl6_9
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f2633,plain,
    ( spl6_218
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_218])])).

fof(f2651,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl6_218 ),
    inference(resolution,[],[f2640,f173])).

fof(f173,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f172,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f172,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f51,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2640,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X1))
        | m1_subset_1(sK3,X1) )
    | ~ spl6_218 ),
    inference(resolution,[],[f2635,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f2635,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl6_218 ),
    inference(avatar_component_clause,[],[f2633])).

fof(f2649,plain,
    ( spl6_10
    | ~ spl6_216 ),
    inference(avatar_split_clause,[],[f2648,f2584,f124])).

fof(f124,plain,
    ( spl6_10
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f2584,plain,
    ( spl6_216
  <=> r2_hidden(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_216])])).

fof(f2648,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl6_216 ),
    inference(resolution,[],[f2613,f173])).

fof(f2613,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1))
        | m1_subset_1(sK3,X1) )
    | ~ spl6_216 ),
    inference(resolution,[],[f2586,f57])).

fof(f2586,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl6_216 ),
    inference(avatar_component_clause,[],[f2584])).

fof(f2636,plain,
    ( spl6_218
    | ~ spl6_16
    | ~ spl6_212 ),
    inference(avatar_split_clause,[],[f2621,f2510,f163,f2633])).

fof(f163,plain,
    ( spl6_16
  <=> r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f2510,plain,
    ( spl6_212
  <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_212])])).

fof(f2621,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl6_16
    | ~ spl6_212 ),
    inference(resolution,[],[f2512,f1261])).

fof(f1261,plain,
    ( ! [X2] :
        ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),X2)
        | r2_hidden(sK3,X2) )
    | ~ spl6_16 ),
    inference(resolution,[],[f165,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f165,plain,
    ( r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f2512,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2))
    | ~ spl6_212 ),
    inference(avatar_component_clause,[],[f2510])).

fof(f2587,plain,
    ( spl6_216
    | ~ spl6_16
    | ~ spl6_208 ),
    inference(avatar_split_clause,[],[f2572,f2491,f163,f2584])).

fof(f2491,plain,
    ( spl6_208
  <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_208])])).

fof(f2572,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl6_16
    | ~ spl6_208 ),
    inference(resolution,[],[f2493,f1261])).

fof(f2493,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl6_208 ),
    inference(avatar_component_clause,[],[f2491])).

fof(f2513,plain,
    ( spl6_212
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f2465,f404,f2510])).

fof(f404,plain,
    ( spl6_44
  <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f2465,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2))
    | ~ spl6_44 ),
    inference(superposition,[],[f455,f406])).

fof(f406,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f404])).

fof(f455,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) ),
    inference(duplicate_literal_removal,[],[f449])).

fof(f449,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)
      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) ) ),
    inference(resolution,[],[f178,f51])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(k1_setfam_1(k2_tarski(X0,X1)),X2),X1)
      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) ) ),
    inference(resolution,[],[f77,f50])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1)))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f62,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f2494,plain,
    ( spl6_208
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f2436,f404,f2491])).

fof(f2436,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl6_44 ),
    inference(superposition,[],[f66,f406])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1258,plain,
    ( spl6_45
    | ~ spl6_54
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f1257,f167,f467,f408])).

fof(f408,plain,
    ( spl6_45
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f467,plain,
    ( spl6_54
  <=> l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f167,plain,
    ( spl6_17
  <=> v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f1257,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl6_17 ),
    inference(resolution,[],[f169,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f169,plain,
    ( v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f167])).

fof(f470,plain,
    ( spl6_54
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f465,f445,f467])).

fof(f445,plain,
    ( spl6_53
  <=> l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f465,plain,
    ( l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl6_53 ),
    inference(resolution,[],[f447,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f447,plain,
    ( l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f445])).

fof(f457,plain,
    ( spl6_2
    | ~ spl6_6
    | spl6_7
    | ~ spl6_3
    | spl6_4
    | ~ spl6_1
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f456,f408,f80,f95,f90,f110,f105,f85])).

fof(f85,plain,
    ( spl6_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f105,plain,
    ( spl6_6
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f110,plain,
    ( spl6_7
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f90,plain,
    ( spl6_3
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f95,plain,
    ( spl6_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f80,plain,
    ( spl6_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f456,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_45 ),
    inference(resolution,[],[f410,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f410,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f408])).

fof(f448,plain,
    ( spl6_53
    | ~ spl6_1
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f402,f295,f80,f445])).

fof(f295,plain,
    ( spl6_29
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f402,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl6_29 ),
    inference(resolution,[],[f297,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f297,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f295])).

fof(f411,plain,
    ( spl6_44
    | spl6_2
    | ~ spl6_21
    | spl6_45
    | spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_3
    | spl6_4
    | ~ spl6_1
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f394,f295,f80,f95,f90,f110,f105,f100,f408,f241,f85,f404])).

fof(f241,plain,
    ( spl6_21
  <=> v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f100,plain,
    ( spl6_5
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f394,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl6_29 ),
    inference(resolution,[],[f297,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(X3)
      | ~ v1_pre_topc(X3)
      | ~ m1_pre_topc(X3,X0)
      | u1_struct_0(X3) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2)))
      | k2_tsep_1(X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(X3)
      | ~ v1_pre_topc(X3)
      | ~ m1_pre_topc(X3,X0)
      | u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f298,plain,
    ( spl6_7
    | spl6_29
    | ~ spl6_6
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f288,f248,f105,f295,f110])).

fof(f248,plain,
    ( spl6_22
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f288,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK2)
    | ~ spl6_6
    | ~ spl6_22 ),
    inference(resolution,[],[f249,f107])).

fof(f107,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)
        | v2_struct_0(X0) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f248])).

fof(f250,plain,
    ( spl6_22
    | spl6_2
    | spl6_4
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f245,f90,f80,f95,f85,f248])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f56,f92])).

fof(f92,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f244,plain,
    ( spl6_7
    | spl6_21
    | ~ spl6_6
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f234,f223,f105,f241,f110])).

fof(f223,plain,
    ( spl6_18
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | v1_pre_topc(k2_tsep_1(sK0,sK1,X0))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f234,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | ~ spl6_6
    | ~ spl6_18 ),
    inference(resolution,[],[f224,f107])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_pre_topc(k2_tsep_1(sK0,sK1,X0))
        | v2_struct_0(X0) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f223])).

fof(f225,plain,
    ( spl6_18
    | spl6_2
    | spl6_4
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f220,f90,f80,f95,f85,f223])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v1_pre_topc(k2_tsep_1(sK0,sK1,X0)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f55,f92])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v1_pre_topc(k2_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f170,plain,
    ( spl6_16
    | spl6_17
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f160,f115,f167,f163])).

fof(f115,plain,
    ( spl6_8
  <=> m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f160,plain,
    ( v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | ~ spl6_8 ),
    inference(resolution,[],[f48,f117])).

fof(f117,plain,
    ( m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f127,plain,
    ( ~ spl6_9
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f74,f124,f120])).

fof(f74,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4] :
      ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X4 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK1))
      | sK3 != X5
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X4 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X5] :
                            ( X3 = X5
                            & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X5] :
                            ( X3 = X5
                            & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                   => ( ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) )
                      & ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tmap_1)).

fof(f118,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f33,f115])).

fof(f33,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f113,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f34,f110])).

fof(f34,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f108,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f35,f105])).

fof(f35,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f103,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f36,f100])).

fof(f36,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f98,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f37,f95])).

fof(f37,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f93,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f38,f90])).

fof(f38,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f88,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f39,f85])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f83,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f40,f80])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:22:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (19102)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.50  % (19101)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.50  % (19110)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.51  % (19120)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (19100)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (19109)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (19095)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (19108)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (19117)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (19111)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (19094)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (19099)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (19113)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (19119)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (19105)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (19116)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (19112)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (19096)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (19116)Refutation not found, incomplete strategy% (19116)------------------------------
% 0.22/0.56  % (19116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (19116)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (19116)Memory used [KB]: 10746
% 0.22/0.56  % (19116)Time elapsed: 0.140 s
% 0.22/0.56  % (19116)------------------------------
% 0.22/0.56  % (19116)------------------------------
% 0.22/0.56  % (19103)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (19123)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.56  % (19122)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.57  % (19107)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.57  % (19104)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.57  % (19104)Refutation not found, incomplete strategy% (19104)------------------------------
% 0.22/0.57  % (19104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (19104)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (19104)Memory used [KB]: 10746
% 0.22/0.57  % (19104)Time elapsed: 0.157 s
% 0.22/0.57  % (19104)------------------------------
% 0.22/0.57  % (19104)------------------------------
% 0.22/0.58  % (19118)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.58  % (19098)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.64/0.59  % (19097)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.64/0.59  % (19110)Refutation found. Thanks to Tanya!
% 1.64/0.59  % SZS status Theorem for theBenchmark
% 1.64/0.59  % SZS output start Proof for theBenchmark
% 1.64/0.59  % (19106)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.64/0.59  fof(f2653,plain,(
% 1.64/0.59    $false),
% 1.64/0.59    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f103,f108,f113,f118,f127,f170,f225,f244,f250,f298,f411,f448,f457,f470,f1258,f2494,f2513,f2587,f2636,f2649,f2652])).
% 1.64/0.59  fof(f2652,plain,(
% 1.64/0.59    spl6_9 | ~spl6_218),
% 1.64/0.59    inference(avatar_split_clause,[],[f2651,f2633,f120])).
% 1.64/0.59  fof(f120,plain,(
% 1.64/0.59    spl6_9 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.64/0.59  fof(f2633,plain,(
% 1.64/0.59    spl6_218 <=> r2_hidden(sK3,u1_struct_0(sK2))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_218])])).
% 1.64/0.59  fof(f2651,plain,(
% 1.64/0.59    m1_subset_1(sK3,u1_struct_0(sK2)) | ~spl6_218),
% 1.64/0.59    inference(resolution,[],[f2640,f173])).
% 1.64/0.59  fof(f173,plain,(
% 1.64/0.59    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.64/0.59    inference(resolution,[],[f172,f52])).
% 1.64/0.59  fof(f52,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f6])).
% 1.64/0.59  fof(f6,axiom,(
% 1.64/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.64/0.59  fof(f172,plain,(
% 1.64/0.59    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.64/0.59    inference(duplicate_literal_removal,[],[f171])).
% 1.64/0.59  fof(f171,plain,(
% 1.64/0.59    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.64/0.59    inference(resolution,[],[f51,f50])).
% 1.64/0.59  fof(f50,plain,(
% 1.64/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f27])).
% 1.64/0.59  fof(f27,plain,(
% 1.64/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.64/0.59    inference(ennf_transformation,[],[f1])).
% 1.64/0.59  fof(f1,axiom,(
% 1.64/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.64/0.59  fof(f51,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f27])).
% 1.64/0.59  fof(f2640,plain,(
% 1.64/0.59    ( ! [X1] : (~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X1)) | m1_subset_1(sK3,X1)) ) | ~spl6_218),
% 1.64/0.59    inference(resolution,[],[f2635,f57])).
% 1.64/0.59  fof(f57,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f31])).
% 1.64/0.59  fof(f31,plain,(
% 1.64/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.64/0.59    inference(flattening,[],[f30])).
% 1.64/0.59  fof(f30,plain,(
% 1.64/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.64/0.59    inference(ennf_transformation,[],[f7])).
% 1.64/0.59  fof(f7,axiom,(
% 1.64/0.59    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.64/0.59  fof(f2635,plain,(
% 1.64/0.59    r2_hidden(sK3,u1_struct_0(sK2)) | ~spl6_218),
% 1.64/0.59    inference(avatar_component_clause,[],[f2633])).
% 1.64/0.59  fof(f2649,plain,(
% 1.64/0.59    spl6_10 | ~spl6_216),
% 1.64/0.59    inference(avatar_split_clause,[],[f2648,f2584,f124])).
% 1.64/0.59  fof(f124,plain,(
% 1.64/0.59    spl6_10 <=> m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.64/0.59  fof(f2584,plain,(
% 1.64/0.59    spl6_216 <=> r2_hidden(sK3,u1_struct_0(sK1))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_216])])).
% 1.64/0.59  fof(f2648,plain,(
% 1.64/0.59    m1_subset_1(sK3,u1_struct_0(sK1)) | ~spl6_216),
% 1.64/0.59    inference(resolution,[],[f2613,f173])).
% 1.64/0.59  fof(f2613,plain,(
% 1.64/0.59    ( ! [X1] : (~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1)) | m1_subset_1(sK3,X1)) ) | ~spl6_216),
% 1.64/0.59    inference(resolution,[],[f2586,f57])).
% 1.64/0.59  fof(f2586,plain,(
% 1.64/0.59    r2_hidden(sK3,u1_struct_0(sK1)) | ~spl6_216),
% 1.64/0.59    inference(avatar_component_clause,[],[f2584])).
% 1.64/0.59  fof(f2636,plain,(
% 1.64/0.59    spl6_218 | ~spl6_16 | ~spl6_212),
% 1.64/0.59    inference(avatar_split_clause,[],[f2621,f2510,f163,f2633])).
% 1.64/0.59  fof(f163,plain,(
% 1.64/0.59    spl6_16 <=> r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.64/0.59  fof(f2510,plain,(
% 1.64/0.59    spl6_212 <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_212])])).
% 1.64/0.59  fof(f2621,plain,(
% 1.64/0.59    r2_hidden(sK3,u1_struct_0(sK2)) | (~spl6_16 | ~spl6_212)),
% 1.64/0.59    inference(resolution,[],[f2512,f1261])).
% 1.64/0.59  fof(f1261,plain,(
% 1.64/0.59    ( ! [X2] : (~r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),X2) | r2_hidden(sK3,X2)) ) | ~spl6_16),
% 1.64/0.59    inference(resolution,[],[f165,f49])).
% 1.64/0.59  fof(f49,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f27])).
% 1.64/0.59  fof(f165,plain,(
% 1.64/0.59    r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) | ~spl6_16),
% 1.64/0.59    inference(avatar_component_clause,[],[f163])).
% 1.64/0.59  fof(f2512,plain,(
% 1.64/0.59    r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2)) | ~spl6_212),
% 1.64/0.59    inference(avatar_component_clause,[],[f2510])).
% 1.64/0.59  fof(f2587,plain,(
% 1.64/0.59    spl6_216 | ~spl6_16 | ~spl6_208),
% 1.64/0.59    inference(avatar_split_clause,[],[f2572,f2491,f163,f2584])).
% 1.64/0.59  fof(f2491,plain,(
% 1.64/0.59    spl6_208 <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_208])])).
% 1.64/0.59  fof(f2572,plain,(
% 1.64/0.59    r2_hidden(sK3,u1_struct_0(sK1)) | (~spl6_16 | ~spl6_208)),
% 1.64/0.59    inference(resolution,[],[f2493,f1261])).
% 1.64/0.59  fof(f2493,plain,(
% 1.64/0.59    r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1)) | ~spl6_208),
% 1.64/0.59    inference(avatar_component_clause,[],[f2491])).
% 1.64/0.59  fof(f2513,plain,(
% 1.64/0.59    spl6_212 | ~spl6_44),
% 1.64/0.59    inference(avatar_split_clause,[],[f2465,f404,f2510])).
% 1.64/0.59  fof(f404,plain,(
% 1.64/0.59    spl6_44 <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 1.64/0.59  fof(f2465,plain,(
% 1.64/0.59    r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2)) | ~spl6_44),
% 1.64/0.59    inference(superposition,[],[f455,f406])).
% 1.64/0.59  fof(f406,plain,(
% 1.64/0.59    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl6_44),
% 1.64/0.59    inference(avatar_component_clause,[],[f404])).
% 1.64/0.59  fof(f455,plain,(
% 1.64/0.59    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) )),
% 1.64/0.59    inference(duplicate_literal_removal,[],[f449])).
% 1.64/0.59  fof(f449,plain,(
% 1.64/0.59    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) )),
% 1.64/0.59    inference(resolution,[],[f178,f51])).
% 1.64/0.59  fof(f178,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (r2_hidden(sK4(k1_setfam_1(k2_tarski(X0,X1)),X2),X1) | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)) )),
% 1.64/0.59    inference(resolution,[],[f77,f50])).
% 1.64/0.59  fof(f77,plain,(
% 1.64/0.59    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1))) | r2_hidden(X3,X1)) )),
% 1.64/0.59    inference(equality_resolution,[],[f68])).
% 1.64/0.59  fof(f68,plain,(
% 1.64/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.64/0.59    inference(definition_unfolding,[],[f62,f47])).
% 1.64/0.59  fof(f47,plain,(
% 1.64/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f4])).
% 1.64/0.59  fof(f4,axiom,(
% 1.64/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.64/0.59  fof(f62,plain,(
% 1.64/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.64/0.59    inference(cnf_transformation,[],[f2])).
% 1.64/0.59  fof(f2,axiom,(
% 1.64/0.59    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.64/0.59  fof(f2494,plain,(
% 1.64/0.59    spl6_208 | ~spl6_44),
% 1.64/0.59    inference(avatar_split_clause,[],[f2436,f404,f2491])).
% 1.64/0.59  fof(f2436,plain,(
% 1.64/0.59    r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1)) | ~spl6_44),
% 1.64/0.59    inference(superposition,[],[f66,f406])).
% 1.64/0.59  fof(f66,plain,(
% 1.64/0.59    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 1.64/0.59    inference(definition_unfolding,[],[f46,f47])).
% 1.64/0.59  fof(f46,plain,(
% 1.64/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f3])).
% 1.64/0.59  fof(f3,axiom,(
% 1.64/0.59    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.64/0.59  fof(f1258,plain,(
% 1.64/0.59    spl6_45 | ~spl6_54 | ~spl6_17),
% 1.64/0.59    inference(avatar_split_clause,[],[f1257,f167,f467,f408])).
% 1.64/0.59  fof(f408,plain,(
% 1.64/0.59    spl6_45 <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 1.64/0.59  fof(f467,plain,(
% 1.64/0.59    spl6_54 <=> l1_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 1.64/0.59  fof(f167,plain,(
% 1.64/0.59    spl6_17 <=> v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.64/0.59  fof(f1257,plain,(
% 1.64/0.59    ~l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl6_17),
% 1.64/0.59    inference(resolution,[],[f169,f43])).
% 1.64/0.59  fof(f43,plain,(
% 1.64/0.59    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f22])).
% 1.64/0.59  fof(f22,plain,(
% 1.64/0.59    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.64/0.59    inference(flattening,[],[f21])).
% 1.64/0.59  fof(f21,plain,(
% 1.64/0.59    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.64/0.59    inference(ennf_transformation,[],[f10])).
% 1.64/0.59  fof(f10,axiom,(
% 1.64/0.59    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.64/0.59  fof(f169,plain,(
% 1.64/0.59    v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) | ~spl6_17),
% 1.64/0.59    inference(avatar_component_clause,[],[f167])).
% 1.64/0.59  fof(f470,plain,(
% 1.64/0.59    spl6_54 | ~spl6_53),
% 1.64/0.59    inference(avatar_split_clause,[],[f465,f445,f467])).
% 1.64/0.59  fof(f445,plain,(
% 1.64/0.59    spl6_53 <=> l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 1.64/0.59  fof(f465,plain,(
% 1.64/0.59    l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl6_53),
% 1.64/0.59    inference(resolution,[],[f447,f41])).
% 1.64/0.59  fof(f41,plain,(
% 1.64/0.59    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f19])).
% 1.64/0.59  fof(f19,plain,(
% 1.64/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.64/0.59    inference(ennf_transformation,[],[f8])).
% 1.64/0.59  fof(f8,axiom,(
% 1.64/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.64/0.59  fof(f447,plain,(
% 1.64/0.59    l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~spl6_53),
% 1.64/0.59    inference(avatar_component_clause,[],[f445])).
% 1.64/0.59  fof(f457,plain,(
% 1.64/0.59    spl6_2 | ~spl6_6 | spl6_7 | ~spl6_3 | spl6_4 | ~spl6_1 | ~spl6_45),
% 1.64/0.59    inference(avatar_split_clause,[],[f456,f408,f80,f95,f90,f110,f105,f85])).
% 1.64/0.59  fof(f85,plain,(
% 1.64/0.59    spl6_2 <=> v2_struct_0(sK0)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.64/0.59  fof(f105,plain,(
% 1.64/0.59    spl6_6 <=> m1_pre_topc(sK2,sK0)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.64/0.59  fof(f110,plain,(
% 1.64/0.59    spl6_7 <=> v2_struct_0(sK2)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.64/0.59  fof(f90,plain,(
% 1.64/0.59    spl6_3 <=> m1_pre_topc(sK1,sK0)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.64/0.59  fof(f95,plain,(
% 1.64/0.59    spl6_4 <=> v2_struct_0(sK1)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.64/0.59  fof(f80,plain,(
% 1.64/0.59    spl6_1 <=> l1_pre_topc(sK0)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.64/0.59  fof(f456,plain,(
% 1.64/0.59    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl6_45),
% 1.64/0.59    inference(resolution,[],[f410,f54])).
% 1.64/0.59  fof(f54,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f29])).
% 1.64/0.59  fof(f29,plain,(
% 1.64/0.59    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.64/0.59    inference(flattening,[],[f28])).
% 1.64/0.59  fof(f28,plain,(
% 1.64/0.59    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.64/0.59    inference(ennf_transformation,[],[f12])).
% 1.64/0.59  fof(f12,axiom,(
% 1.64/0.59    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 1.64/0.59  fof(f410,plain,(
% 1.64/0.59    v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl6_45),
% 1.64/0.59    inference(avatar_component_clause,[],[f408])).
% 1.64/0.59  fof(f448,plain,(
% 1.64/0.59    spl6_53 | ~spl6_1 | ~spl6_29),
% 1.64/0.59    inference(avatar_split_clause,[],[f402,f295,f80,f445])).
% 1.64/0.59  fof(f295,plain,(
% 1.64/0.59    spl6_29 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 1.64/0.59  fof(f402,plain,(
% 1.64/0.59    ~l1_pre_topc(sK0) | l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~spl6_29),
% 1.64/0.59    inference(resolution,[],[f297,f42])).
% 1.64/0.59  fof(f42,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f20])).
% 1.64/0.59  fof(f20,plain,(
% 1.64/0.59    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.64/0.59    inference(ennf_transformation,[],[f9])).
% 1.64/0.59  fof(f9,axiom,(
% 1.64/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.64/0.59  fof(f297,plain,(
% 1.64/0.59    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | ~spl6_29),
% 1.64/0.59    inference(avatar_component_clause,[],[f295])).
% 1.64/0.59  fof(f411,plain,(
% 1.64/0.59    spl6_44 | spl6_2 | ~spl6_21 | spl6_45 | spl6_5 | ~spl6_6 | spl6_7 | ~spl6_3 | spl6_4 | ~spl6_1 | ~spl6_29),
% 1.64/0.59    inference(avatar_split_clause,[],[f394,f295,f80,f95,f90,f110,f105,f100,f408,f241,f85,f404])).
% 1.64/0.59  fof(f241,plain,(
% 1.64/0.59    spl6_21 <=> v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.64/0.59  fof(f100,plain,(
% 1.64/0.59    spl6_5 <=> r1_tsep_1(sK1,sK2)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.64/0.59  fof(f394,plain,(
% 1.64/0.59    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(sK1,sK2) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0) | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl6_29),
% 1.64/0.59    inference(resolution,[],[f297,f75])).
% 1.64/0.59  fof(f75,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X1,X2) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2)))) )),
% 1.64/0.59    inference(equality_resolution,[],[f64])).
% 1.64/0.59  fof(f64,plain,(
% 1.64/0.59    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X1,X2) | v2_struct_0(X3) | ~v1_pre_topc(X3) | ~m1_pre_topc(X3,X0) | u1_struct_0(X3) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2))) | k2_tsep_1(X0,X1,X2) != X3) )),
% 1.64/0.59    inference(definition_unfolding,[],[f45,f47])).
% 1.64/0.59  fof(f45,plain,(
% 1.64/0.59    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X1,X2) | v2_struct_0(X3) | ~v1_pre_topc(X3) | ~m1_pre_topc(X3,X0) | u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3) )),
% 1.64/0.59    inference(cnf_transformation,[],[f24])).
% 1.64/0.59  fof(f24,plain,(
% 1.64/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.64/0.59    inference(flattening,[],[f23])).
% 1.64/0.59  fof(f23,plain,(
% 1.64/0.59    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.64/0.59    inference(ennf_transformation,[],[f11])).
% 1.64/0.59  fof(f11,axiom,(
% 1.64/0.59    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).
% 1.64/0.59  fof(f298,plain,(
% 1.64/0.59    spl6_7 | spl6_29 | ~spl6_6 | ~spl6_22),
% 1.64/0.59    inference(avatar_split_clause,[],[f288,f248,f105,f295,f110])).
% 1.64/0.59  fof(f248,plain,(
% 1.64/0.59    spl6_22 <=> ! [X0] : (v2_struct_0(X0) | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) | ~m1_pre_topc(X0,sK0))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.64/0.59  fof(f288,plain,(
% 1.64/0.59    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK2) | (~spl6_6 | ~spl6_22)),
% 1.64/0.59    inference(resolution,[],[f249,f107])).
% 1.64/0.59  fof(f107,plain,(
% 1.64/0.59    m1_pre_topc(sK2,sK0) | ~spl6_6),
% 1.64/0.59    inference(avatar_component_clause,[],[f105])).
% 1.64/0.59  fof(f249,plain,(
% 1.64/0.59    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0) | v2_struct_0(X0)) ) | ~spl6_22),
% 1.64/0.59    inference(avatar_component_clause,[],[f248])).
% 1.64/0.59  fof(f250,plain,(
% 1.64/0.59    spl6_22 | spl6_2 | spl6_4 | ~spl6_1 | ~spl6_3),
% 1.64/0.59    inference(avatar_split_clause,[],[f245,f90,f80,f95,f85,f248])).
% 1.64/0.59  fof(f245,plain,(
% 1.64/0.59    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),sK0)) ) | ~spl6_3),
% 1.64/0.59    inference(resolution,[],[f56,f92])).
% 1.64/0.59  fof(f92,plain,(
% 1.64/0.59    m1_pre_topc(sK1,sK0) | ~spl6_3),
% 1.64/0.59    inference(avatar_component_clause,[],[f90])).
% 1.64/0.59  fof(f56,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f29])).
% 1.64/0.59  fof(f244,plain,(
% 1.64/0.59    spl6_7 | spl6_21 | ~spl6_6 | ~spl6_18),
% 1.64/0.59    inference(avatar_split_clause,[],[f234,f223,f105,f241,f110])).
% 1.64/0.59  fof(f223,plain,(
% 1.64/0.59    spl6_18 <=> ! [X0] : (v2_struct_0(X0) | v1_pre_topc(k2_tsep_1(sK0,sK1,X0)) | ~m1_pre_topc(X0,sK0))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.64/0.59  fof(f234,plain,(
% 1.64/0.59    v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK2) | (~spl6_6 | ~spl6_18)),
% 1.64/0.59    inference(resolution,[],[f224,f107])).
% 1.64/0.59  fof(f224,plain,(
% 1.64/0.59    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_pre_topc(k2_tsep_1(sK0,sK1,X0)) | v2_struct_0(X0)) ) | ~spl6_18),
% 1.64/0.59    inference(avatar_component_clause,[],[f223])).
% 1.64/0.59  fof(f225,plain,(
% 1.64/0.59    spl6_18 | spl6_2 | spl6_4 | ~spl6_1 | ~spl6_3),
% 1.64/0.59    inference(avatar_split_clause,[],[f220,f90,f80,f95,f85,f223])).
% 1.64/0.59  fof(f220,plain,(
% 1.64/0.59    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v1_pre_topc(k2_tsep_1(sK0,sK1,X0))) ) | ~spl6_3),
% 1.64/0.59    inference(resolution,[],[f55,f92])).
% 1.64/0.59  fof(f55,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v1_pre_topc(k2_tsep_1(X0,X1,X2))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f29])).
% 1.64/0.59  fof(f170,plain,(
% 1.64/0.59    spl6_16 | spl6_17 | ~spl6_8),
% 1.64/0.59    inference(avatar_split_clause,[],[f160,f115,f167,f163])).
% 1.64/0.59  fof(f115,plain,(
% 1.64/0.59    spl6_8 <=> m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.64/0.59  fof(f160,plain,(
% 1.64/0.59    v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) | r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) | ~spl6_8),
% 1.64/0.59    inference(resolution,[],[f48,f117])).
% 1.64/0.59  fof(f117,plain,(
% 1.64/0.59    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) | ~spl6_8),
% 1.64/0.59    inference(avatar_component_clause,[],[f115])).
% 1.64/0.59  fof(f48,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f26])).
% 1.64/0.59  fof(f26,plain,(
% 1.64/0.59    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.64/0.59    inference(flattening,[],[f25])).
% 1.64/0.59  fof(f25,plain,(
% 1.64/0.59    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.64/0.59    inference(ennf_transformation,[],[f5])).
% 1.64/0.59  fof(f5,axiom,(
% 1.64/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.64/0.59  fof(f127,plain,(
% 1.64/0.59    ~spl6_9 | ~spl6_10),
% 1.64/0.59    inference(avatar_split_clause,[],[f74,f124,f120])).
% 1.64/0.59  fof(f74,plain,(
% 1.64/0.59    ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.64/0.59    inference(equality_resolution,[],[f73])).
% 1.64/0.59  fof(f73,plain,(
% 1.64/0.59    ( ! [X4] : (~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_subset_1(X4,u1_struct_0(sK2)) | sK3 != X4) )),
% 1.64/0.59    inference(equality_resolution,[],[f32])).
% 1.64/0.59  fof(f32,plain,(
% 1.64/0.59    ( ! [X4,X5] : (~m1_subset_1(X5,u1_struct_0(sK1)) | sK3 != X5 | ~m1_subset_1(X4,u1_struct_0(sK2)) | sK3 != X4) )),
% 1.64/0.59    inference(cnf_transformation,[],[f18])).
% 1.64/0.59  fof(f18,plain,(
% 1.64/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.64/0.59    inference(flattening,[],[f17])).
% 1.64/0.59  fof(f17,plain,(
% 1.64/0.59    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.64/0.59    inference(ennf_transformation,[],[f16])).
% 1.64/0.59  fof(f16,plain,(
% 1.64/0.59    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 1.64/0.59    inference(pure_predicate_removal,[],[f15])).
% 1.64/0.59  fof(f15,plain,(
% 1.64/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 1.64/0.59    inference(rectify,[],[f14])).
% 1.64/0.59  fof(f14,negated_conjecture,(
% 1.64/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 1.64/0.59    inference(negated_conjecture,[],[f13])).
% 1.64/0.59  fof(f13,conjecture,(
% 1.64/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tmap_1)).
% 1.64/0.59  fof(f118,plain,(
% 1.64/0.59    spl6_8),
% 1.64/0.59    inference(avatar_split_clause,[],[f33,f115])).
% 1.64/0.59  fof(f33,plain,(
% 1.64/0.59    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))),
% 1.64/0.59    inference(cnf_transformation,[],[f18])).
% 1.64/0.59  fof(f113,plain,(
% 1.64/0.59    ~spl6_7),
% 1.64/0.59    inference(avatar_split_clause,[],[f34,f110])).
% 1.64/0.59  fof(f34,plain,(
% 1.64/0.59    ~v2_struct_0(sK2)),
% 1.64/0.59    inference(cnf_transformation,[],[f18])).
% 1.64/0.59  fof(f108,plain,(
% 1.64/0.59    spl6_6),
% 1.64/0.59    inference(avatar_split_clause,[],[f35,f105])).
% 1.64/0.59  fof(f35,plain,(
% 1.64/0.59    m1_pre_topc(sK2,sK0)),
% 1.64/0.59    inference(cnf_transformation,[],[f18])).
% 1.64/0.59  fof(f103,plain,(
% 1.64/0.59    ~spl6_5),
% 1.64/0.59    inference(avatar_split_clause,[],[f36,f100])).
% 1.64/0.59  fof(f36,plain,(
% 1.64/0.59    ~r1_tsep_1(sK1,sK2)),
% 1.64/0.59    inference(cnf_transformation,[],[f18])).
% 1.64/0.59  fof(f98,plain,(
% 1.64/0.59    ~spl6_4),
% 1.64/0.59    inference(avatar_split_clause,[],[f37,f95])).
% 1.64/0.59  fof(f37,plain,(
% 1.64/0.59    ~v2_struct_0(sK1)),
% 1.64/0.59    inference(cnf_transformation,[],[f18])).
% 1.64/0.59  fof(f93,plain,(
% 1.64/0.59    spl6_3),
% 1.64/0.59    inference(avatar_split_clause,[],[f38,f90])).
% 1.64/0.59  fof(f38,plain,(
% 1.64/0.59    m1_pre_topc(sK1,sK0)),
% 1.64/0.59    inference(cnf_transformation,[],[f18])).
% 1.64/0.59  fof(f88,plain,(
% 1.64/0.59    ~spl6_2),
% 1.64/0.59    inference(avatar_split_clause,[],[f39,f85])).
% 1.64/0.59  fof(f39,plain,(
% 1.64/0.59    ~v2_struct_0(sK0)),
% 1.64/0.59    inference(cnf_transformation,[],[f18])).
% 1.64/0.59  fof(f83,plain,(
% 1.64/0.59    spl6_1),
% 1.64/0.59    inference(avatar_split_clause,[],[f40,f80])).
% 1.64/0.59  fof(f40,plain,(
% 1.64/0.59    l1_pre_topc(sK0)),
% 1.64/0.59    inference(cnf_transformation,[],[f18])).
% 1.64/0.59  % SZS output end Proof for theBenchmark
% 1.64/0.59  % (19110)------------------------------
% 1.64/0.59  % (19110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (19110)Termination reason: Refutation
% 1.64/0.59  
% 1.64/0.59  % (19110)Memory used [KB]: 12920
% 1.64/0.59  % (19110)Time elapsed: 0.148 s
% 1.64/0.59  % (19110)------------------------------
% 1.64/0.59  % (19110)------------------------------
% 1.64/0.59  % (19093)Success in time 0.217 s
%------------------------------------------------------------------------------
