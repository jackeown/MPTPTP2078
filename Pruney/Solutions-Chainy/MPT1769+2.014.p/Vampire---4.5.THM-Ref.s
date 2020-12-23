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
% DateTime   : Thu Dec  3 13:18:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 336 expanded)
%              Number of leaves         :   45 ( 148 expanded)
%              Depth                    :    9
%              Number of atoms          :  651 (2458 expanded)
%              Number of equality atoms :   51 ( 141 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f691,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f99,f104,f109,f119,f129,f134,f139,f159,f164,f169,f174,f179,f188,f189,f196,f209,f231,f306,f328,f396,f407,f437,f451,f551,f578,f587,f594,f603,f680,f687,f690])).

fof(f690,plain,
    ( sK0 != sK3
    | sK4 != sK6
    | k2_tmap_1(sK0,sK1,sK4,sK2) != k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f687,plain,
    ( sK0 != sK3
    | sK4 != sK6
    | k2_tmap_1(sK0,sK1,sK4,sK2) != k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f680,plain,
    ( spl10_93
    | ~ spl10_7
    | ~ spl10_80
    | ~ spl10_84 ),
    inference(avatar_split_clause,[],[f675,f592,f548,f106,f677])).

fof(f677,plain,
    ( spl10_93
  <=> k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_93])])).

fof(f106,plain,
    ( spl10_7
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f548,plain,
    ( spl10_80
  <=> k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f592,plain,
    ( spl10_84
  <=> ! [X2] :
        ( k3_tmap_1(sK0,sK1,sK0,X2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X2))
        | ~ m1_pre_topc(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f675,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | ~ spl10_7
    | ~ spl10_80
    | ~ spl10_84 ),
    inference(forward_demodulation,[],[f673,f550])).

fof(f550,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl10_80 ),
    inference(avatar_component_clause,[],[f548])).

fof(f673,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl10_7
    | ~ spl10_84 ),
    inference(resolution,[],[f593,f108])).

fof(f108,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f593,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK0)
        | k3_tmap_1(sK0,sK1,sK0,X2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X2)) )
    | ~ spl10_84 ),
    inference(avatar_component_clause,[],[f592])).

fof(f603,plain,
    ( spl10_6
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_52
    | ~ spl10_82 ),
    inference(avatar_split_clause,[],[f601,f563,f369,f96,f91,f101])).

fof(f101,plain,
    ( spl10_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f91,plain,
    ( spl10_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f96,plain,
    ( spl10_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f369,plain,
    ( spl10_52
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f563,plain,
    ( spl10_82
  <=> u1_struct_0(sK1) = sK7(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).

fof(f601,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_82 ),
    inference(superposition,[],[f56,f565])).

fof(f565,plain,
    ( u1_struct_0(sK1) = sK7(sK1)
    | ~ spl10_82 ),
    inference(avatar_component_clause,[],[f563])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK7(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(f594,plain,
    ( ~ spl10_5
    | ~ spl10_4
    | ~ spl10_12
    | ~ spl10_13
    | spl10_6
    | spl10_84
    | ~ spl10_11
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f589,f435,f126,f592,f101,f136,f131,f91,f96])).

% (2236)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f131,plain,
    ( spl10_12
  <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f136,plain,
    ( spl10_13
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f126,plain,
    ( spl10_11
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f435,plain,
    ( spl10_64
  <=> ! [X3,X5,X4] :
        ( v2_struct_0(X3)
        | k3_tmap_1(sK0,X3,sK0,X4,X5) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X3),X5,u1_struct_0(X4))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X3))
        | ~ m1_pre_topc(X4,sK0)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f589,plain,
    ( ! [X2] :
        ( k3_tmap_1(sK0,sK1,sK0,X2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X2))
        | v2_struct_0(sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X2,sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1) )
    | ~ spl10_11
    | ~ spl10_64 ),
    inference(resolution,[],[f436,f128])).

% (2256)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f128,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f436,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
        | k3_tmap_1(sK0,X3,sK0,X4,X5) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X3),X5,u1_struct_0(X4))
        | v2_struct_0(X3)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X3))
        | ~ m1_pre_topc(X4,sK0)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl10_64 ),
    inference(avatar_component_clause,[],[f435])).

fof(f587,plain,
    ( spl10_82
    | ~ spl10_56
    | ~ spl10_66 ),
    inference(avatar_split_clause,[],[f586,f448,f386,f563])).

fof(f386,plain,
    ( spl10_56
  <=> sP9(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

% (2247)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f448,plain,
    ( spl10_66
  <=> sP9(sK7(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f586,plain,
    ( u1_struct_0(sK1) = sK7(sK1)
    | ~ spl10_56
    | ~ spl10_66 ),
    inference(resolution,[],[f579,f506])).

fof(f506,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK7(sK1))
        | sK7(sK1) = X2 )
    | ~ spl10_66 ),
    inference(resolution,[],[f502,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f502,plain,
    ( ! [X0] : r1_tarski(sK7(sK1),X0)
    | ~ spl10_66 ),
    inference(resolution,[],[f450,f238])).

fof(f238,plain,(
    ! [X0,X1] :
      ( ~ sP9(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f62,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP9(X1) ) ),
    inference(general_splitting,[],[f66,f72_D])).

fof(f72,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP9(X1) ) ),
    inference(cnf_transformation,[],[f72_D])).

fof(f72_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP9(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f450,plain,
    ( sP9(sK7(sK1))
    | ~ spl10_66 ),
    inference(avatar_component_clause,[],[f448])).

fof(f579,plain,
    ( ! [X0] : r1_tarski(u1_struct_0(sK1),X0)
    | ~ spl10_56 ),
    inference(resolution,[],[f388,f238])).

fof(f388,plain,
    ( sP9(u1_struct_0(sK1))
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f386])).

fof(f578,plain,
    ( spl10_56
    | ~ spl10_52 ),
    inference(avatar_split_clause,[],[f577,f369,f386])).

fof(f577,plain,
    ( sP9(u1_struct_0(sK1))
    | ~ spl10_52 ),
    inference(resolution,[],[f371,f242])).

fof(f242,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sP9(X0) ) ),
    inference(resolution,[],[f72,f210])).

fof(f210,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f64,f69])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f371,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f369])).

fof(f551,plain,
    ( spl10_80
    | ~ spl10_7
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f545,f405,f106,f548])).

fof(f405,plain,
    ( spl10_58
  <=> ! [X3] :
        ( ~ m1_pre_topc(X3,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f545,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl10_7
    | ~ spl10_58 ),
    inference(resolution,[],[f406,f108])).

fof(f406,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(X3,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X3)) )
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f405])).

fof(f451,plain,
    ( spl10_66
    | ~ spl10_52
    | ~ spl10_45 ),
    inference(avatar_split_clause,[],[f445,f325,f369,f448])).

fof(f325,plain,
    ( spl10_45
  <=> m1_subset_1(sK7(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f445,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | sP9(sK7(sK1))
    | ~ spl10_45 ),
    inference(resolution,[],[f327,f72])).

fof(f327,plain,
    ( m1_subset_1(sK7(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f325])).

fof(f437,plain,
    ( spl10_3
    | spl10_64
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f429,f193,f81,f76,f435,f86])).

fof(f86,plain,
    ( spl10_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f76,plain,
    ( spl10_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f81,plain,
    ( spl10_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f193,plain,
    ( spl10_24
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f429,plain,
    ( ! [X4,X5,X3] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X4,sK0)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X3))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
        | k3_tmap_1(sK0,X3,sK0,X4,X5) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X3),X5,u1_struct_0(X4)) )
    | ~ spl10_24 ),
    inference(duplicate_literal_removal,[],[f426])).

fof(f426,plain,
    ( ! [X4,X5,X3] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X4,sK0)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X3))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
        | ~ m1_pre_topc(X4,sK0)
        | k3_tmap_1(sK0,X3,sK0,X4,X5) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X3),X5,u1_struct_0(X4)) )
    | ~ spl10_24 ),
    inference(resolution,[],[f53,f195])).

fof(f195,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f193])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f407,plain,
    ( spl10_58
    | spl10_3
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f401,f126,f81,f76,f101,f96,f91,f136,f131,f86,f405])).

fof(f401,plain,
    ( ! [X3] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X3,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X3)) )
    | ~ spl10_11 ),
    inference(resolution,[],[f54,f128])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f396,plain,
    ( spl10_57
    | ~ spl10_29
    | ~ spl10_26
    | ~ spl10_21
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_52
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f391,f303,f369,f136,f131,f126,f176,f206,f228,f393])).

fof(f393,plain,
    ( spl10_57
  <=> sK4 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).

fof(f228,plain,
    ( spl10_29
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f206,plain,
    ( spl10_26
  <=> v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f176,plain,
    ( spl10_21
  <=> v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f303,plain,
    ( spl10_42
  <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f391,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = sK6
    | ~ spl10_42 ),
    inference(duplicate_literal_removal,[],[f390])).

fof(f390,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = sK6
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_42 ),
    inference(resolution,[],[f68,f305])).

fof(f305,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f303])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | X4 = X5
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f328,plain,
    ( spl10_45
    | spl10_6
    | ~ spl10_5
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f318,f91,f96,f101,f325])).

fof(f318,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(sK7(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_4 ),
    inference(resolution,[],[f55,f93])).

fof(f93,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f306,plain,
    ( spl10_42
    | ~ spl10_17
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f301,f161,f156,f303])).

fof(f156,plain,
    ( spl10_17
  <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f161,plain,
    ( spl10_18
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f301,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)
    | ~ spl10_17
    | ~ spl10_18 ),
    inference(forward_demodulation,[],[f158,f163])).

fof(f163,plain,
    ( sK0 = sK3
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f158,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f156])).

fof(f231,plain,
    ( spl10_29
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f226,f166,f161,f228])).

fof(f166,plain,
    ( spl10_19
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f226,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(forward_demodulation,[],[f168,f163])).

fof(f168,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f166])).

fof(f209,plain,
    ( spl10_26
    | ~ spl10_18
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f204,f171,f161,f206])).

fof(f171,plain,
    ( spl10_20
  <=> v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f204,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl10_18
    | ~ spl10_20 ),
    inference(forward_demodulation,[],[f173,f163])).

fof(f173,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f171])).

fof(f196,plain,
    ( spl10_24
    | ~ spl10_9
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f190,f161,f116,f193])).

fof(f116,plain,
    ( spl10_9
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f190,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl10_9
    | ~ spl10_18 ),
    inference(backward_demodulation,[],[f118,f163])).

fof(f118,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f189,plain,
    ( spl10_22
    | spl10_23 ),
    inference(avatar_split_clause,[],[f29,f185,f181])).

fof(f181,plain,
    ( spl10_22
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f185,plain,
    ( spl10_23
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f29,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                    & X0 = X3 )
                                 => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                  <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ! [X6] :
                              ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X6) )
                             => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                  & X0 = X3 )
                               => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tmap_1)).

fof(f188,plain,
    ( ~ spl10_22
    | ~ spl10_23 ),
    inference(avatar_split_clause,[],[f30,f185,f181])).

fof(f30,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f15])).

fof(f179,plain,(
    spl10_21 ),
    inference(avatar_split_clause,[],[f31,f176])).

fof(f31,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f15])).

fof(f174,plain,(
    spl10_20 ),
    inference(avatar_split_clause,[],[f32,f171])).

fof(f32,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f169,plain,(
    spl10_19 ),
    inference(avatar_split_clause,[],[f33,f166])).

fof(f33,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f164,plain,(
    spl10_18 ),
    inference(avatar_split_clause,[],[f34,f161])).

fof(f34,plain,(
    sK0 = sK3 ),
    inference(cnf_transformation,[],[f15])).

fof(f159,plain,(
    spl10_17 ),
    inference(avatar_split_clause,[],[f35,f156])).

fof(f35,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
    inference(cnf_transformation,[],[f15])).

fof(f139,plain,(
    spl10_13 ),
    inference(avatar_split_clause,[],[f39,f136])).

fof(f39,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f134,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f40,f131])).

fof(f40,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f129,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f41,f126])).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f119,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f43,f116])).

fof(f43,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f109,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f45,f106])).

fof(f45,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f104,plain,(
    ~ spl10_6 ),
    inference(avatar_split_clause,[],[f46,f101])).

fof(f46,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f99,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f47,f96])).

fof(f47,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f94,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f48,f91])).

fof(f48,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f49,f86])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f84,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f50,f81])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f51,f76])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:56:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (2232)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (2254)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (2223)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (2226)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (2224)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (2229)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (2225)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (2237)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (2231)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (2246)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (2241)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (2222)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (2242)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (2237)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (2245)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (2252)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (2244)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (2221)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (2255)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (2235)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (2252)Refutation not found, incomplete strategy% (2252)------------------------------
% 0.21/0.53  % (2252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2252)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2252)Memory used [KB]: 10874
% 0.21/0.54  % (2252)Time elapsed: 0.126 s
% 0.21/0.54  % (2252)------------------------------
% 0.21/0.54  % (2252)------------------------------
% 0.21/0.54  % (2229)Refutation not found, incomplete strategy% (2229)------------------------------
% 0.21/0.54  % (2229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2229)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2229)Memory used [KB]: 10874
% 0.21/0.54  % (2229)Time elapsed: 0.134 s
% 0.21/0.54  % (2229)------------------------------
% 0.21/0.54  % (2229)------------------------------
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f691,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f99,f104,f109,f119,f129,f134,f139,f159,f164,f169,f174,f179,f188,f189,f196,f209,f231,f306,f328,f396,f407,f437,f451,f551,f578,f587,f594,f603,f680,f687,f690])).
% 0.21/0.54  fof(f690,plain,(
% 0.21/0.54    sK0 != sK3 | sK4 != sK6 | k2_tmap_1(sK0,sK1,sK4,sK2) != k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f687,plain,(
% 0.21/0.54    sK0 != sK3 | sK4 != sK6 | k2_tmap_1(sK0,sK1,sK4,sK2) != k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f680,plain,(
% 0.21/0.54    spl10_93 | ~spl10_7 | ~spl10_80 | ~spl10_84),
% 0.21/0.54    inference(avatar_split_clause,[],[f675,f592,f548,f106,f677])).
% 0.21/0.54  fof(f677,plain,(
% 0.21/0.54    spl10_93 <=> k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_93])])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    spl10_7 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.54  fof(f548,plain,(
% 0.21/0.54    spl10_80 <=> k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).
% 0.21/0.54  fof(f592,plain,(
% 0.21/0.54    spl10_84 <=> ! [X2] : (k3_tmap_1(sK0,sK1,sK0,X2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X2)) | ~m1_pre_topc(X2,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).
% 0.21/0.54  fof(f675,plain,(
% 0.21/0.54    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | (~spl10_7 | ~spl10_80 | ~spl10_84)),
% 0.21/0.54    inference(forward_demodulation,[],[f673,f550])).
% 0.21/0.54  fof(f550,plain,(
% 0.21/0.54    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~spl10_80),
% 0.21/0.54    inference(avatar_component_clause,[],[f548])).
% 0.21/0.54  fof(f673,plain,(
% 0.21/0.54    k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (~spl10_7 | ~spl10_84)),
% 0.21/0.54    inference(resolution,[],[f593,f108])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    m1_pre_topc(sK2,sK0) | ~spl10_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f106])).
% 0.21/0.54  fof(f593,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_pre_topc(X2,sK0) | k3_tmap_1(sK0,sK1,sK0,X2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X2))) ) | ~spl10_84),
% 0.21/0.54    inference(avatar_component_clause,[],[f592])).
% 0.21/0.54  fof(f603,plain,(
% 0.21/0.54    spl10_6 | ~spl10_4 | ~spl10_5 | ~spl10_52 | ~spl10_82),
% 0.21/0.54    inference(avatar_split_clause,[],[f601,f563,f369,f96,f91,f101])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    spl10_6 <=> v2_struct_0(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    spl10_4 <=> l1_pre_topc(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    spl10_5 <=> v2_pre_topc(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.54  fof(f369,plain,(
% 0.21/0.54    spl10_52 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).
% 0.21/0.54  fof(f563,plain,(
% 0.21/0.54    spl10_82 <=> u1_struct_0(sK1) = sK7(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).
% 0.21/0.54  fof(f601,plain,(
% 0.21/0.54    ~v1_xboole_0(u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~spl10_82),
% 0.21/0.54    inference(superposition,[],[f56,f565])).
% 0.21/0.54  fof(f565,plain,(
% 0.21/0.54    u1_struct_0(sK1) = sK7(sK1) | ~spl10_82),
% 0.21/0.54    inference(avatar_component_clause,[],[f563])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(sK7(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).
% 0.21/0.54  fof(f594,plain,(
% 0.21/0.54    ~spl10_5 | ~spl10_4 | ~spl10_12 | ~spl10_13 | spl10_6 | spl10_84 | ~spl10_11 | ~spl10_64),
% 0.21/0.54    inference(avatar_split_clause,[],[f589,f435,f126,f592,f101,f136,f131,f91,f96])).
% 0.21/0.54  % (2236)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    spl10_12 <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    spl10_13 <=> v1_funct_1(sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    spl10_11 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.21/0.54  fof(f435,plain,(
% 0.21/0.54    spl10_64 <=> ! [X3,X5,X4] : (v2_struct_0(X3) | k3_tmap_1(sK0,X3,sK0,X4,X5) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X3),X5,u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X3)) | ~m1_pre_topc(X4,sK0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).
% 0.21/0.54  fof(f589,plain,(
% 0.21/0.54    ( ! [X2] : (k3_tmap_1(sK0,sK1,sK0,X2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X2)) | v2_struct_0(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)) ) | (~spl10_11 | ~spl10_64)),
% 0.21/0.54    inference(resolution,[],[f436,f128])).
% 0.21/0.54  % (2256)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl10_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f126])).
% 0.21/0.54  fof(f436,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | k3_tmap_1(sK0,X3,sK0,X4,X5) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X3),X5,u1_struct_0(X4)) | v2_struct_0(X3) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X3)) | ~m1_pre_topc(X4,sK0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | ~spl10_64),
% 0.21/0.54    inference(avatar_component_clause,[],[f435])).
% 0.21/0.54  fof(f587,plain,(
% 0.21/0.54    spl10_82 | ~spl10_56 | ~spl10_66),
% 0.21/0.54    inference(avatar_split_clause,[],[f586,f448,f386,f563])).
% 0.21/0.54  fof(f386,plain,(
% 0.21/0.54    spl10_56 <=> sP9(u1_struct_0(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).
% 0.21/0.54  % (2247)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  fof(f448,plain,(
% 0.21/0.54    spl10_66 <=> sP9(sK7(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).
% 0.21/0.54  fof(f586,plain,(
% 0.21/0.54    u1_struct_0(sK1) = sK7(sK1) | (~spl10_56 | ~spl10_66)),
% 0.21/0.54    inference(resolution,[],[f579,f506])).
% 0.21/0.54  fof(f506,plain,(
% 0.21/0.54    ( ! [X2] : (~r1_tarski(X2,sK7(sK1)) | sK7(sK1) = X2) ) | ~spl10_66),
% 0.21/0.54    inference(resolution,[],[f502,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f502,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(sK7(sK1),X0)) ) | ~spl10_66),
% 0.21/0.54    inference(resolution,[],[f450,f238])).
% 0.21/0.54  fof(f238,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~sP9(X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(resolution,[],[f62,f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP9(X1)) )),
% 0.21/0.54    inference(general_splitting,[],[f66,f72_D])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP9(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f72_D])).
% 0.21/0.54  fof(f72_D,plain,(
% 0.21/0.54    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP9(X1)) )),
% 0.21/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f450,plain,(
% 0.21/0.54    sP9(sK7(sK1)) | ~spl10_66),
% 0.21/0.54    inference(avatar_component_clause,[],[f448])).
% 0.21/0.54  fof(f579,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(u1_struct_0(sK1),X0)) ) | ~spl10_56),
% 0.21/0.54    inference(resolution,[],[f388,f238])).
% 0.21/0.54  fof(f388,plain,(
% 0.21/0.54    sP9(u1_struct_0(sK1)) | ~spl10_56),
% 0.21/0.54    inference(avatar_component_clause,[],[f386])).
% 0.21/0.54  fof(f578,plain,(
% 0.21/0.54    spl10_56 | ~spl10_52),
% 0.21/0.54    inference(avatar_split_clause,[],[f577,f369,f386])).
% 0.21/0.54  fof(f577,plain,(
% 0.21/0.54    sP9(u1_struct_0(sK1)) | ~spl10_52),
% 0.21/0.54    inference(resolution,[],[f371,f242])).
% 0.21/0.54  fof(f242,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(X0) | sP9(X0)) )),
% 0.21/0.54    inference(resolution,[],[f72,f210])).
% 0.21/0.54  fof(f210,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(resolution,[],[f64,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f371,plain,(
% 0.21/0.54    v1_xboole_0(u1_struct_0(sK1)) | ~spl10_52),
% 0.21/0.54    inference(avatar_component_clause,[],[f369])).
% 0.21/0.54  fof(f551,plain,(
% 0.21/0.54    spl10_80 | ~spl10_7 | ~spl10_58),
% 0.21/0.54    inference(avatar_split_clause,[],[f545,f405,f106,f548])).
% 0.21/0.54  fof(f405,plain,(
% 0.21/0.54    spl10_58 <=> ! [X3] : (~m1_pre_topc(X3,sK0) | k2_tmap_1(sK0,sK1,sK4,X3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X3)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).
% 0.21/0.54  fof(f545,plain,(
% 0.21/0.54    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (~spl10_7 | ~spl10_58)),
% 0.21/0.54    inference(resolution,[],[f406,f108])).
% 0.21/0.54  fof(f406,plain,(
% 0.21/0.54    ( ! [X3] : (~m1_pre_topc(X3,sK0) | k2_tmap_1(sK0,sK1,sK4,X3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X3))) ) | ~spl10_58),
% 0.21/0.54    inference(avatar_component_clause,[],[f405])).
% 0.21/0.54  fof(f451,plain,(
% 0.21/0.54    spl10_66 | ~spl10_52 | ~spl10_45),
% 0.21/0.54    inference(avatar_split_clause,[],[f445,f325,f369,f448])).
% 0.21/0.54  fof(f325,plain,(
% 0.21/0.54    spl10_45 <=> m1_subset_1(sK7(sK1),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).
% 0.21/0.54  fof(f445,plain,(
% 0.21/0.54    ~v1_xboole_0(u1_struct_0(sK1)) | sP9(sK7(sK1)) | ~spl10_45),
% 0.21/0.54    inference(resolution,[],[f327,f72])).
% 0.21/0.54  fof(f327,plain,(
% 0.21/0.54    m1_subset_1(sK7(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl10_45),
% 0.21/0.54    inference(avatar_component_clause,[],[f325])).
% 0.21/0.54  fof(f437,plain,(
% 0.21/0.54    spl10_3 | spl10_64 | ~spl10_1 | ~spl10_2 | ~spl10_24),
% 0.21/0.54    inference(avatar_split_clause,[],[f429,f193,f81,f76,f435,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    spl10_3 <=> v2_struct_0(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    spl10_1 <=> l1_pre_topc(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    spl10_2 <=> v2_pre_topc(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.54  fof(f193,plain,(
% 0.21/0.54    spl10_24 <=> m1_pre_topc(sK0,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).
% 0.21/0.54  fof(f429,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(sK0) | ~m1_pre_topc(X4,sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | k3_tmap_1(sK0,X3,sK0,X4,X5) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X3),X5,u1_struct_0(X4))) ) | ~spl10_24),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f426])).
% 0.21/0.54  fof(f426,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(sK0) | ~m1_pre_topc(X4,sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~m1_pre_topc(X4,sK0) | k3_tmap_1(sK0,X3,sK0,X4,X5) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X3),X5,u1_struct_0(X4))) ) | ~spl10_24),
% 0.21/0.54    inference(resolution,[],[f53,f195])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    m1_pre_topc(sK0,sK0) | ~spl10_24),
% 0.21/0.54    inference(avatar_component_clause,[],[f193])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (~m1_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.21/0.54  fof(f407,plain,(
% 0.21/0.54    spl10_58 | spl10_3 | ~spl10_12 | ~spl10_13 | ~spl10_4 | ~spl10_5 | spl10_6 | ~spl10_1 | ~spl10_2 | ~spl10_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f401,f126,f81,f76,f101,f96,f91,f136,f131,f86,f405])).
% 0.21/0.54  fof(f401,plain,(
% 0.21/0.54    ( ! [X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK0) | ~m1_pre_topc(X3,sK0) | k2_tmap_1(sK0,sK1,sK4,X3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X3))) ) | ~spl10_11),
% 0.21/0.54    inference(resolution,[],[f54,f128])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.21/0.54  fof(f396,plain,(
% 0.21/0.54    spl10_57 | ~spl10_29 | ~spl10_26 | ~spl10_21 | ~spl10_11 | ~spl10_12 | ~spl10_13 | spl10_52 | ~spl10_42),
% 0.21/0.54    inference(avatar_split_clause,[],[f391,f303,f369,f136,f131,f126,f176,f206,f228,f393])).
% 0.21/0.54  fof(f393,plain,(
% 0.21/0.54    spl10_57 <=> sK4 = sK6),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).
% 0.21/0.54  fof(f228,plain,(
% 0.21/0.54    spl10_29 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 0.21/0.54  fof(f206,plain,(
% 0.21/0.54    spl10_26 <=> v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    spl10_21 <=> v1_funct_1(sK6)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.21/0.54  fof(f303,plain,(
% 0.21/0.54    spl10_42 <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).
% 0.21/0.54  fof(f391,plain,(
% 0.21/0.54    v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK6) | ~v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = sK6 | ~spl10_42),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f390])).
% 0.21/0.54  fof(f390,plain,(
% 0.21/0.54    v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK6) | ~v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = sK6 | v1_xboole_0(u1_struct_0(sK1)) | ~spl10_42),
% 0.21/0.54    inference(resolution,[],[f68,f305])).
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6) | ~spl10_42),
% 0.21/0.54    inference(avatar_component_clause,[],[f303])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_funct_2(X0,X1,X2,X3,X4,X5) | v1_xboole_0(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | X4 = X5 | v1_xboole_0(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.21/0.54    inference(flattening,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 0.21/0.54  fof(f328,plain,(
% 0.21/0.54    spl10_45 | spl10_6 | ~spl10_5 | ~spl10_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f318,f91,f96,f101,f325])).
% 0.21/0.54  fof(f318,plain,(
% 0.21/0.54    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | m1_subset_1(sK7(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl10_4),
% 0.21/0.54    inference(resolution,[],[f55,f93])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    l1_pre_topc(sK1) | ~spl10_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f91])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f306,plain,(
% 0.21/0.54    spl10_42 | ~spl10_17 | ~spl10_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f301,f161,f156,f303])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    spl10_17 <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    spl10_18 <=> sK0 = sK3),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.21/0.54  fof(f301,plain,(
% 0.21/0.54    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6) | (~spl10_17 | ~spl10_18)),
% 0.21/0.54    inference(forward_demodulation,[],[f158,f163])).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    sK0 = sK3 | ~spl10_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f161])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) | ~spl10_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f156])).
% 0.21/0.54  fof(f231,plain,(
% 0.21/0.54    spl10_29 | ~spl10_18 | ~spl10_19),
% 0.21/0.54    inference(avatar_split_clause,[],[f226,f166,f161,f228])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    spl10_19 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.21/0.54  fof(f226,plain,(
% 0.21/0.54    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (~spl10_18 | ~spl10_19)),
% 0.21/0.54    inference(forward_demodulation,[],[f168,f163])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl10_19),
% 0.21/0.54    inference(avatar_component_clause,[],[f166])).
% 0.21/0.54  fof(f209,plain,(
% 0.21/0.54    spl10_26 | ~spl10_18 | ~spl10_20),
% 0.21/0.54    inference(avatar_split_clause,[],[f204,f171,f161,f206])).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    spl10_20 <=> v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.21/0.54  fof(f204,plain,(
% 0.21/0.54    v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl10_18 | ~spl10_20)),
% 0.21/0.54    inference(forward_demodulation,[],[f173,f163])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl10_20),
% 0.21/0.54    inference(avatar_component_clause,[],[f171])).
% 0.21/0.54  fof(f196,plain,(
% 0.21/0.54    spl10_24 | ~spl10_9 | ~spl10_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f190,f161,f116,f193])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    spl10_9 <=> m1_pre_topc(sK3,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.54  fof(f190,plain,(
% 0.21/0.54    m1_pre_topc(sK0,sK0) | (~spl10_9 | ~spl10_18)),
% 0.21/0.54    inference(backward_demodulation,[],[f118,f163])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    m1_pre_topc(sK3,sK0) | ~spl10_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f116])).
% 0.21/0.54  fof(f189,plain,(
% 0.21/0.54    spl10_22 | spl10_23),
% 0.21/0.54    inference(avatar_split_clause,[],[f29,f185,f181])).
% 0.21/0.54  fof(f181,plain,(
% 0.21/0.54    spl10_22 <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.21/0.54  fof(f185,plain,(
% 0.21/0.54    spl10_23 <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f11])).
% 0.21/0.54  fof(f11,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tmap_1)).
% 0.21/0.54  fof(f188,plain,(
% 0.21/0.54    ~spl10_22 | ~spl10_23),
% 0.21/0.54    inference(avatar_split_clause,[],[f30,f185,f181])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f179,plain,(
% 0.21/0.54    spl10_21),
% 0.21/0.54    inference(avatar_split_clause,[],[f31,f176])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    v1_funct_1(sK6)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    spl10_20),
% 0.21/0.54    inference(avatar_split_clause,[],[f32,f171])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    spl10_19),
% 0.21/0.54    inference(avatar_split_clause,[],[f33,f166])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    spl10_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f34,f161])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    sK0 = sK3),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    spl10_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f35,f156])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    spl10_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f39,f136])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    v1_funct_1(sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    spl10_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f40,f131])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    spl10_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f41,f126])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    spl10_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f43,f116])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    m1_pre_topc(sK3,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    spl10_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f45,f106])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    m1_pre_topc(sK2,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ~spl10_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f46,f101])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ~v2_struct_0(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    spl10_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f47,f96])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    v2_pre_topc(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    spl10_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f48,f91])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    l1_pre_topc(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ~spl10_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f49,f86])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ~v2_struct_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    spl10_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f50,f81])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    v2_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    spl10_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f51,f76])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    l1_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (2237)------------------------------
% 0.21/0.54  % (2237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2237)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (2237)Memory used [KB]: 11257
% 0.21/0.54  % (2237)Time elapsed: 0.129 s
% 0.21/0.54  % (2237)------------------------------
% 0.21/0.54  % (2237)------------------------------
% 0.21/0.54  % (2233)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (2220)Success in time 0.186 s
%------------------------------------------------------------------------------
