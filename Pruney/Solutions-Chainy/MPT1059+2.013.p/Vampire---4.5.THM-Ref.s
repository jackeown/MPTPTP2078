%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 189 expanded)
%              Number of leaves         :   26 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  364 ( 638 expanded)
%              Number of equality atoms :   63 (  98 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f83,f89,f96,f107,f129,f138,f146,f152,f170,f181,f184,f193])).

fof(f193,plain,
    ( ~ spl4_6
    | spl4_18 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl4_6
    | spl4_18 ),
    inference(resolution,[],[f186,f88])).

fof(f88,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f186,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | spl4_18 ),
    inference(resolution,[],[f180,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f180,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl4_18
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f184,plain,
    ( spl4_3
    | ~ spl4_4
    | spl4_17 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl4_3
    | ~ spl4_4
    | spl4_17 ),
    inference(subsumption_resolution,[],[f182,f73])).

fof(f73,plain,
    ( m1_subset_1(sK3,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f182,plain,
    ( ~ m1_subset_1(sK3,sK0)
    | spl4_3
    | spl4_17 ),
    inference(resolution,[],[f176,f78])).

fof(f78,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ m1_subset_1(X0,sK0) )
    | spl4_3 ),
    inference(resolution,[],[f68,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f68,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f176,plain,
    ( ~ r2_hidden(sK3,sK0)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl4_17
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f181,plain,
    ( ~ spl4_17
    | ~ spl4_18
    | ~ spl4_12
    | ~ spl4_14
    | spl4_16 ),
    inference(avatar_split_clause,[],[f172,f167,f144,f135,f178,f174])).

fof(f135,plain,
    ( spl4_12
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f144,plain,
    ( spl4_14
  <=> ! [X3,X4] :
        ( ~ v5_relat_1(sK2,X3)
        | k7_partfun1(X3,sK2,X4) = k1_funct_1(sK2,X4)
        | ~ r2_hidden(X4,k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f167,plain,
    ( spl4_16
  <=> k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f172,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ r2_hidden(sK3,sK0)
    | ~ spl4_12
    | ~ spl4_14
    | spl4_16 ),
    inference(trivial_inequality_removal,[],[f171])).

fof(f171,plain,
    ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,sK3)
    | ~ v5_relat_1(sK2,sK1)
    | ~ r2_hidden(sK3,sK0)
    | ~ spl4_12
    | ~ spl4_14
    | spl4_16 ),
    inference(superposition,[],[f169,f153])).

fof(f153,plain,
    ( ! [X4,X3] :
        ( k7_partfun1(X3,sK2,X4) = k1_funct_1(sK2,X4)
        | ~ v5_relat_1(sK2,X3)
        | ~ r2_hidden(X4,sK0) )
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f145,f137])).

fof(f137,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f135])).

fof(f145,plain,
    ( ! [X4,X3] :
        ( ~ v5_relat_1(sK2,X3)
        | k7_partfun1(X3,sK2,X4) = k1_funct_1(sK2,X4)
        | ~ r2_hidden(X4,k1_relat_1(sK2)) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f169,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f167])).

fof(f170,plain,
    ( ~ spl4_16
    | ~ spl4_1
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f165,f93,f86,f80,f71,f66,f56,f167])).

fof(f56,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f80,plain,
    ( spl4_5
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f93,plain,
    ( spl4_7
  <=> k3_funct_2(sK0,sK1,sK2,sK3) = k7_partfun1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f165,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | ~ spl4_1
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(subsumption_resolution,[],[f164,f73])).

fof(f164,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | ~ m1_subset_1(sK3,sK0)
    | ~ spl4_1
    | spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(superposition,[],[f95,f150])).

fof(f150,plain,
    ( ! [X0] :
        ( k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_1
    | spl4_3
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f149,f68])).

fof(f149,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0) )
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f148,f82])).

fof(f82,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,sK0,sK1)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0) )
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(resolution,[],[f75,f88])).

fof(f75,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X2,X0)
        | k3_funct_2(X0,X1,sK2,X2) = k1_funct_1(sK2,X2) )
    | ~ spl4_1 ),
    inference(resolution,[],[f58,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f58,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f95,plain,
    ( k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f152,plain,
    ( ~ spl4_6
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl4_6
    | spl4_13 ),
    inference(resolution,[],[f147,f88])).

fof(f147,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_13 ),
    inference(resolution,[],[f142,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f142,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl4_13
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f146,plain,
    ( ~ spl4_13
    | spl4_14
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f76,f56,f144,f140])).

fof(f76,plain,
    ( ! [X4,X3] :
        ( ~ v5_relat_1(sK2,X3)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X4,k1_relat_1(sK2))
        | k7_partfun1(X3,sK2,X4) = k1_funct_1(sK2,X4) )
    | ~ spl4_1 ),
    inference(resolution,[],[f58,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f138,plain,
    ( spl4_12
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f132,f100,f86,f135])).

fof(f100,plain,
    ( spl4_8
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f132,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f130,f88])).

fof(f130,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_8 ),
    inference(superposition,[],[f102,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f102,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f129,plain,
    ( spl4_2
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl4_2
    | ~ spl4_9 ),
    inference(resolution,[],[f114,f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(o_1_0_wellord2(X0),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(o_1_0_wellord2(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_1_0_wellord2)).

fof(f114,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k1_xboole_0)
    | spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f112,f34])).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f112,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_xboole_0) )
    | spl4_2
    | ~ spl4_9 ),
    inference(superposition,[],[f91,f106])).

fof(f106,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ m1_subset_1(X0,sK1) )
    | spl4_2 ),
    inference(resolution,[],[f77,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f77,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,sK1) )
    | spl4_2 ),
    inference(resolution,[],[f63,f36])).

fof(f63,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f107,plain,
    ( spl4_8
    | spl4_9
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f98,f86,f80,f104,f100])).

fof(f98,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f84,f88])).

fof(f84,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_5 ),
    inference(resolution,[],[f82,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f96,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f28,f93])).

fof(f28,plain,(
    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

fof(f89,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f31,f86])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f83,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f30,f80])).

fof(f30,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f27,f71])).

fof(f27,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f33,f66])).

fof(f33,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f32,f61])).

fof(f32,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f29,f56])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (10364)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (10374)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (10365)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (10370)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (10362)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (10362)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f83,f89,f96,f107,f129,f138,f146,f152,f170,f181,f184,f193])).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    ~spl4_6 | spl4_18),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f192])).
% 0.20/0.49  fof(f192,plain,(
% 0.20/0.49    $false | (~spl4_6 | spl4_18)),
% 0.20/0.49    inference(resolution,[],[f186,f88])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | spl4_18),
% 0.20/0.49    inference(resolution,[],[f180,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    ~v5_relat_1(sK2,sK1) | spl4_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f178])).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    spl4_18 <=> v5_relat_1(sK2,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.49  fof(f184,plain,(
% 0.20/0.49    spl4_3 | ~spl4_4 | spl4_17),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f183])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    $false | (spl4_3 | ~spl4_4 | spl4_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f182,f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    m1_subset_1(sK3,sK0) | ~spl4_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    spl4_4 <=> m1_subset_1(sK3,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    ~m1_subset_1(sK3,sK0) | (spl4_3 | spl4_17)),
% 0.20/0.49    inference(resolution,[],[f176,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(X0,sK0) | ~m1_subset_1(X0,sK0)) ) | spl4_3),
% 0.20/0.49    inference(resolution,[],[f68,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ~v1_xboole_0(sK0) | spl4_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    spl4_3 <=> v1_xboole_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.49  fof(f176,plain,(
% 0.20/0.49    ~r2_hidden(sK3,sK0) | spl4_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f174])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    spl4_17 <=> r2_hidden(sK3,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.49  fof(f181,plain,(
% 0.20/0.49    ~spl4_17 | ~spl4_18 | ~spl4_12 | ~spl4_14 | spl4_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f172,f167,f144,f135,f178,f174])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    spl4_12 <=> sK0 = k1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    spl4_14 <=> ! [X3,X4] : (~v5_relat_1(sK2,X3) | k7_partfun1(X3,sK2,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,k1_relat_1(sK2)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    spl4_16 <=> k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    ~v5_relat_1(sK2,sK1) | ~r2_hidden(sK3,sK0) | (~spl4_12 | ~spl4_14 | spl4_16)),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f171])).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    k1_funct_1(sK2,sK3) != k1_funct_1(sK2,sK3) | ~v5_relat_1(sK2,sK1) | ~r2_hidden(sK3,sK0) | (~spl4_12 | ~spl4_14 | spl4_16)),
% 0.20/0.49    inference(superposition,[],[f169,f153])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    ( ! [X4,X3] : (k7_partfun1(X3,sK2,X4) = k1_funct_1(sK2,X4) | ~v5_relat_1(sK2,X3) | ~r2_hidden(X4,sK0)) ) | (~spl4_12 | ~spl4_14)),
% 0.20/0.49    inference(forward_demodulation,[],[f145,f137])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    sK0 = k1_relat_1(sK2) | ~spl4_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f135])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    ( ! [X4,X3] : (~v5_relat_1(sK2,X3) | k7_partfun1(X3,sK2,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,k1_relat_1(sK2))) ) | ~spl4_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f144])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) | spl4_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f167])).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    ~spl4_16 | ~spl4_1 | spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f165,f93,f86,f80,f71,f66,f56,f167])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl4_1 <=> v1_funct_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    spl4_5 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    spl4_7 <=> k3_funct_2(sK0,sK1,sK2,sK3) = k7_partfun1(sK1,sK2,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) | (~spl4_1 | spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f164,f73])).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) | ~m1_subset_1(sK3,sK0) | (~spl4_1 | spl4_3 | ~spl4_5 | ~spl4_6 | spl4_7)),
% 0.20/0.49    inference(superposition,[],[f95,f150])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    ( ! [X0] : (k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0) | ~m1_subset_1(X0,sK0)) ) | (~spl4_1 | spl4_3 | ~spl4_5 | ~spl4_6)),
% 0.20/0.49    inference(subsumption_resolution,[],[f149,f68])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    ( ! [X0] : (v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)) ) | (~spl4_1 | ~spl4_5 | ~spl4_6)),
% 0.20/0.49    inference(subsumption_resolution,[],[f148,f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    v1_funct_2(sK2,sK0,sK1) | ~spl4_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f80])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_2(sK2,sK0,sK1) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)) ) | (~spl4_1 | ~spl4_6)),
% 0.20/0.49    inference(resolution,[],[f75,f88])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X2,X0) | k3_funct_2(X0,X1,sK2,X2) = k1_funct_1(sK2,X2)) ) | ~spl4_1),
% 0.20/0.49    inference(resolution,[],[f58,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    v1_funct_1(sK2) | ~spl4_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f56])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3) | spl4_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f93])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    ~spl4_6 | spl4_13),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f151])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    $false | (~spl4_6 | spl4_13)),
% 0.20/0.49    inference(resolution,[],[f147,f88])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_13),
% 0.20/0.49    inference(resolution,[],[f142,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    ~v1_relat_1(sK2) | spl4_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f140])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    spl4_13 <=> v1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    ~spl4_13 | spl4_14 | ~spl4_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f76,f56,f144,f140])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X4,X3] : (~v5_relat_1(sK2,X3) | ~v1_relat_1(sK2) | ~r2_hidden(X4,k1_relat_1(sK2)) | k7_partfun1(X3,sK2,X4) = k1_funct_1(sK2,X4)) ) | ~spl4_1),
% 0.20/0.49    inference(resolution,[],[f58,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    spl4_12 | ~spl4_6 | ~spl4_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f132,f100,f86,f135])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    spl4_8 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    sK0 = k1_relat_1(sK2) | (~spl4_6 | ~spl4_8)),
% 0.20/0.49    inference(subsumption_resolution,[],[f130,f88])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_8),
% 0.20/0.49    inference(superposition,[],[f102,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f100])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    spl4_2 | ~spl4_9),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f128])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    $false | (spl4_2 | ~spl4_9)),
% 0.20/0.49    inference(resolution,[],[f114,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(o_1_0_wellord2(X0),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : m1_subset_1(o_1_0_wellord2(X0),X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_1_0_wellord2)).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_xboole_0)) ) | (spl4_2 | ~spl4_9)),
% 0.20/0.49    inference(subsumption_resolution,[],[f112,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~m1_subset_1(X0,k1_xboole_0)) ) | (spl4_2 | ~spl4_9)),
% 0.20/0.49    inference(superposition,[],[f91,f106])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | ~spl4_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    spl4_9 <=> k1_xboole_0 = sK1),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(sK1,X0) | ~m1_subset_1(X0,sK1)) ) | spl4_2),
% 0.20/0.49    inference(resolution,[],[f77,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,sK1)) ) | spl4_2),
% 0.20/0.49    inference(resolution,[],[f63,f36])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ~v1_xboole_0(sK1) | spl4_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    spl4_2 <=> v1_xboole_0(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    spl4_8 | spl4_9 | ~spl4_5 | ~spl4_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f98,f86,f80,f104,f100])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl4_5 | ~spl4_6)),
% 0.20/0.49    inference(subsumption_resolution,[],[f84,f88])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_5),
% 0.20/0.49    inference(resolution,[],[f82,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    ~spl4_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f28,f93])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3) & m1_subset_1(X3,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.20/0.49    inference(negated_conjecture,[],[f11])).
% 0.20/0.49  fof(f11,conjecture,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    spl4_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f31,f86])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    spl4_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f30,f80])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f27,f71])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    m1_subset_1(sK3,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ~spl4_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f33,f66])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ~v1_xboole_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ~spl4_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f32,f61])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ~v1_xboole_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    spl4_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f29,f56])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    v1_funct_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (10362)------------------------------
% 0.20/0.49  % (10362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (10362)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (10362)Memory used [KB]: 10618
% 0.20/0.49  % (10362)Time elapsed: 0.076 s
% 0.20/0.49  % (10362)------------------------------
% 0.20/0.49  % (10362)------------------------------
% 0.20/0.49  % (10361)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (10355)Success in time 0.134 s
%------------------------------------------------------------------------------
