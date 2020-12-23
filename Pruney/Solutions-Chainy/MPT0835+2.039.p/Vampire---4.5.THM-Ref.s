%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 252 expanded)
%              Number of leaves         :   38 ( 112 expanded)
%              Depth                    :    8
%              Number of atoms          :  371 ( 585 expanded)
%              Number of equality atoms :  102 ( 160 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (32558)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f256,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f69,f78,f92,f101,f114,f120,f129,f135,f140,f145,f149,f154,f160,f164,f191,f197,f203,f219,f226,f234,f252,f255])).

fof(f255,plain,
    ( ~ spl4_13
    | ~ spl4_14
    | spl4_28 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | ~ spl4_13
    | ~ spl4_14
    | spl4_28 ),
    inference(subsumption_resolution,[],[f253,f139])).

fof(f139,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl4_13
  <=> k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f253,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2)
    | ~ spl4_14
    | spl4_28 ),
    inference(superposition,[],[f251,f144])).

fof(f144,plain,
    ( ! [X0] : k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_14
  <=> ! [X0] : k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f251,plain,
    ( k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl4_28
  <=> k1_relat_1(sK2) = k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f252,plain,
    ( ~ spl4_28
    | ~ spl4_8
    | spl4_11
    | ~ spl4_17
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f242,f162,f157,f126,f111,f249])).

fof(f111,plain,
    ( spl4_8
  <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f126,plain,
    ( spl4_11
  <=> k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) = k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f157,plain,
    ( spl4_17
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f162,plain,
    ( spl4_18
  <=> ! [X0] : k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f242,plain,
    ( k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))
    | ~ spl4_8
    | spl4_11
    | ~ spl4_17
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f241,f159])).

fof(f159,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK1)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f157])).

fof(f241,plain,
    ( k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1))
    | ~ spl4_8
    | spl4_11
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f240,f163])).

fof(f163,plain,
    ( ! [X0] : k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f162])).

fof(f240,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
    | ~ spl4_8
    | spl4_11 ),
    inference(forward_demodulation,[],[f128,f113])).

fof(f113,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f128,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f234,plain,
    ( ~ spl4_15
    | spl4_23
    | ~ spl4_26 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl4_15
    | spl4_23
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f232,f196])).

fof(f196,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl4_23
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f232,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_15
    | ~ spl4_26 ),
    inference(superposition,[],[f148,f225])).

fof(f225,plain,
    ( sK2 = k7_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl4_26
  <=> sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f148,plain,
    ( ! [X3] : k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl4_15
  <=> ! [X3] : k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f226,plain,
    ( spl4_26
    | ~ spl4_2
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f221,f216,f66,f223])).

fof(f66,plain,
    ( spl4_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f216,plain,
    ( spl4_25
  <=> v4_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f221,plain,
    ( sK2 = k7_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_2
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f220,f68])).

fof(f68,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f220,plain,
    ( sK2 = k7_relat_1(sK2,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_25 ),
    inference(resolution,[],[f218,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f218,plain,
    ( v4_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f216])).

fof(f219,plain,
    ( spl4_25
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f206,f200,f216])).

fof(f200,plain,
    ( spl4_24
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f206,plain,
    ( v4_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_24 ),
    inference(resolution,[],[f202,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f202,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f200])).

fof(f203,plain,
    ( spl4_24
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f198,f89,f200])).

fof(f89,plain,
    ( spl4_5
  <=> sP3(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f198,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))
    | ~ spl4_5 ),
    inference(resolution,[],[f102,f91])).

fof(f91,plain,
    ( sP3(sK2,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) ) ),
    inference(resolution,[],[f56,f53])).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f56,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(k1_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ sP3(X3,X2) ) ),
    inference(general_splitting,[],[f52,f55_D])).

fof(f55,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | sP3(X3,X2) ) ),
    inference(cnf_transformation,[],[f55_D])).

fof(f55_D,plain,(
    ! [X2,X3] :
      ( ! [X0] : ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
    <=> ~ sP3(X3,X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f197,plain,
    ( ~ spl4_23
    | ~ spl4_18
    | spl4_22 ),
    inference(avatar_split_clause,[],[f192,f188,f162,f194])).

fof(f188,plain,
    ( spl4_22
  <=> k2_relat_1(sK2) = k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f192,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_18
    | spl4_22 ),
    inference(superposition,[],[f190,f163])).

fof(f190,plain,
    ( k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f188])).

fof(f191,plain,
    ( ~ spl4_22
    | ~ spl4_1
    | ~ spl4_8
    | ~ spl4_14
    | spl4_16 ),
    inference(avatar_split_clause,[],[f181,f151,f143,f111,f58,f188])).

fof(f58,plain,
    ( spl4_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f151,plain,
    ( spl4_16
  <=> k2_relat_1(sK2) = k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f181,plain,
    ( k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_8
    | ~ spl4_14
    | spl4_16 ),
    inference(backward_demodulation,[],[f153,f180])).

fof(f180,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK0)
    | ~ spl4_1
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f179,f113])).

fof(f179,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k10_relat_1(sK2,sK0)
    | ~ spl4_1
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f115,f144])).

fof(f115,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k8_relset_1(sK1,sK0,sK2,sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f49,f60])).

fof(f60,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f153,plain,
    ( k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f151])).

fof(f164,plain,
    ( spl4_18
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f108,f58,f162])).

fof(f108,plain,
    ( ! [X0] : k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl4_1 ),
    inference(resolution,[],[f51,f60])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f160,plain,
    ( spl4_17
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f155,f147,f98,f157])).

fof(f98,plain,
    ( spl4_6
  <=> sK2 = k7_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f155,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK1)
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(superposition,[],[f148,f100])).

fof(f100,plain,
    ( sK2 = k7_relat_1(sK2,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f154,plain,
    ( ~ spl4_16
    | ~ spl4_1
    | spl4_12 ),
    inference(avatar_split_clause,[],[f141,f132,f58,f151])).

fof(f132,plain,
    ( spl4_12
  <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f141,plain,
    ( k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0))
    | ~ spl4_1
    | spl4_12 ),
    inference(backward_demodulation,[],[f134,f103])).

fof(f103,plain,
    ( ! [X0] : k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl4_1 ),
    inference(resolution,[],[f50,f60])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f134,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f132])).

fof(f149,plain,
    ( spl4_15
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f87,f66,f147])).

fof(f87,plain,
    ( ! [X3] : k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3)
    | ~ spl4_2 ),
    inference(resolution,[],[f39,f68])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f145,plain,
    ( spl4_14
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f103,f58,f143])).

fof(f140,plain,
    ( spl4_13
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f71,f66,f137])).

fof(f71,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f68,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f135,plain,
    ( ~ spl4_12
    | ~ spl4_9
    | spl4_10 ),
    inference(avatar_split_clause,[],[f130,f122,f117,f132])).

fof(f117,plain,
    ( spl4_9
  <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f122,plain,
    ( spl4_10
  <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) = k2_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f130,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | ~ spl4_9
    | spl4_10 ),
    inference(backward_demodulation,[],[f124,f119])).

fof(f119,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f124,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f129,plain,
    ( ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f35,f126,f122])).

fof(f35,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f30])).

% (32551)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
          | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
        | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
        | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
          & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

fof(f120,plain,
    ( spl4_9
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f96,f58,f117])).

fof(f96,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f45,f60])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f114,plain,
    ( spl4_8
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f95,f58,f111])).

fof(f95,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f44,f60])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f101,plain,
    ( spl4_6
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f94,f75,f66,f98])).

fof(f75,plain,
    ( spl4_3
  <=> v4_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f94,plain,
    ( sK2 = k7_relat_1(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f93,f68])).

fof(f93,plain,
    ( sK2 = k7_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f40,f77])).

fof(f77,plain,
    ( v4_relat_1(sK2,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f92,plain,
    ( spl4_5
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f80,f58,f89])).

fof(f80,plain,
    ( sP3(sK2,sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f55,f60])).

fof(f78,plain,
    ( spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f73,f58,f75])).

fof(f73,plain,
    ( v4_relat_1(sK2,sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f46,f60])).

fof(f69,plain,
    ( spl4_2
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f63,f58,f66])).

fof(f63,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f62,f60])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f37,f38])).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f61,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f34,f58])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (32534)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (32538)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.49  % (32554)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.49  % (32532)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.49  % (32532)Refutation not found, incomplete strategy% (32532)------------------------------
% 0.20/0.49  % (32532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (32533)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (32532)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (32532)Memory used [KB]: 10618
% 0.20/0.49  % (32532)Time elapsed: 0.087 s
% 0.20/0.49  % (32532)------------------------------
% 0.20/0.49  % (32532)------------------------------
% 0.20/0.49  % (32547)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (32533)Refutation not found, incomplete strategy% (32533)------------------------------
% 0.20/0.50  % (32533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (32534)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (32546)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (32539)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (32540)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.50  % (32543)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (32553)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.50  % (32555)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (32535)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (32537)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (32533)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (32533)Memory used [KB]: 10618
% 0.20/0.50  % (32533)Time elapsed: 0.095 s
% 0.20/0.50  % (32533)------------------------------
% 0.20/0.50  % (32533)------------------------------
% 0.20/0.50  % (32542)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (32546)Refutation not found, incomplete strategy% (32546)------------------------------
% 0.20/0.51  % (32546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (32546)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (32546)Memory used [KB]: 6140
% 0.20/0.51  % (32546)Time elapsed: 0.106 s
% 0.20/0.51  % (32546)------------------------------
% 0.20/0.51  % (32546)------------------------------
% 0.20/0.51  % (32550)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (32538)Refutation not found, incomplete strategy% (32538)------------------------------
% 0.20/0.51  % (32538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (32538)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (32538)Memory used [KB]: 10618
% 0.20/0.51  % (32538)Time elapsed: 0.104 s
% 0.20/0.51  % (32538)------------------------------
% 0.20/0.51  % (32538)------------------------------
% 0.20/0.51  % (32557)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.51  % (32536)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (32552)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  % (32558)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.51  fof(f256,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f61,f69,f78,f92,f101,f114,f120,f129,f135,f140,f145,f149,f154,f160,f164,f191,f197,f203,f219,f226,f234,f252,f255])).
% 0.20/0.51  fof(f255,plain,(
% 0.20/0.51    ~spl4_13 | ~spl4_14 | spl4_28),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f254])).
% 0.20/0.51  fof(f254,plain,(
% 0.20/0.51    $false | (~spl4_13 | ~spl4_14 | spl4_28)),
% 0.20/0.51    inference(subsumption_resolution,[],[f253,f139])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) | ~spl4_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f137])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    spl4_13 <=> k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.51  fof(f253,plain,(
% 0.20/0.51    k10_relat_1(sK2,k2_relat_1(sK2)) != k1_relat_1(sK2) | (~spl4_14 | spl4_28)),
% 0.20/0.51    inference(superposition,[],[f251,f144])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    ( ! [X0] : (k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0)) ) | ~spl4_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f143])).
% 0.20/0.51  fof(f143,plain,(
% 0.20/0.51    spl4_14 <=> ! [X0] : k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.51  fof(f251,plain,(
% 0.20/0.51    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) | spl4_28),
% 0.20/0.51    inference(avatar_component_clause,[],[f249])).
% 0.20/0.51  fof(f249,plain,(
% 0.20/0.51    spl4_28 <=> k1_relat_1(sK2) = k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.51  fof(f252,plain,(
% 0.20/0.51    ~spl4_28 | ~spl4_8 | spl4_11 | ~spl4_17 | ~spl4_18),
% 0.20/0.51    inference(avatar_split_clause,[],[f242,f162,f157,f126,f111,f249])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    spl4_8 <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    spl4_11 <=> k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) = k1_relset_1(sK1,sK0,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.51  fof(f157,plain,(
% 0.20/0.51    spl4_17 <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    spl4_18 <=> ! [X0] : k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.51  fof(f242,plain,(
% 0.20/0.51    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) | (~spl4_8 | spl4_11 | ~spl4_17 | ~spl4_18)),
% 0.20/0.51    inference(forward_demodulation,[],[f241,f159])).
% 0.20/0.51  fof(f159,plain,(
% 0.20/0.51    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) | ~spl4_17),
% 0.20/0.51    inference(avatar_component_clause,[],[f157])).
% 0.20/0.51  fof(f241,plain,(
% 0.20/0.51    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) | (~spl4_8 | spl4_11 | ~spl4_18)),
% 0.20/0.51    inference(forward_demodulation,[],[f240,f163])).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    ( ! [X0] : (k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0)) ) | ~spl4_18),
% 0.20/0.51    inference(avatar_component_clause,[],[f162])).
% 0.20/0.51  fof(f240,plain,(
% 0.20/0.51    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) | (~spl4_8 | spl4_11)),
% 0.20/0.51    inference(forward_demodulation,[],[f128,f113])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl4_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f111])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | spl4_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f126])).
% 0.20/0.51  fof(f234,plain,(
% 0.20/0.51    ~spl4_15 | spl4_23 | ~spl4_26),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f233])).
% 0.20/0.51  fof(f233,plain,(
% 0.20/0.51    $false | (~spl4_15 | spl4_23 | ~spl4_26)),
% 0.20/0.51    inference(subsumption_resolution,[],[f232,f196])).
% 0.20/0.51  fof(f196,plain,(
% 0.20/0.51    k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2)) | spl4_23),
% 0.20/0.51    inference(avatar_component_clause,[],[f194])).
% 0.20/0.51  fof(f194,plain,(
% 0.20/0.51    spl4_23 <=> k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.51  fof(f232,plain,(
% 0.20/0.51    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) | (~spl4_15 | ~spl4_26)),
% 0.20/0.51    inference(superposition,[],[f148,f225])).
% 0.20/0.51  fof(f225,plain,(
% 0.20/0.51    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) | ~spl4_26),
% 0.20/0.51    inference(avatar_component_clause,[],[f223])).
% 0.20/0.51  fof(f223,plain,(
% 0.20/0.51    spl4_26 <=> sK2 = k7_relat_1(sK2,k1_relat_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.51  fof(f148,plain,(
% 0.20/0.51    ( ! [X3] : (k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3)) ) | ~spl4_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f147])).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    spl4_15 <=> ! [X3] : k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.51  fof(f226,plain,(
% 0.20/0.51    spl4_26 | ~spl4_2 | ~spl4_25),
% 0.20/0.51    inference(avatar_split_clause,[],[f221,f216,f66,f223])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    spl4_2 <=> v1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    spl4_25 <=> v4_relat_1(sK2,k1_relat_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.51  fof(f221,plain,(
% 0.20/0.51    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) | (~spl4_2 | ~spl4_25)),
% 0.20/0.51    inference(subsumption_resolution,[],[f220,f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    v1_relat_1(sK2) | ~spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f66])).
% 0.20/0.51  fof(f220,plain,(
% 0.20/0.51    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_25),
% 0.20/0.51    inference(resolution,[],[f218,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.51  fof(f218,plain,(
% 0.20/0.51    v4_relat_1(sK2,k1_relat_1(sK2)) | ~spl4_25),
% 0.20/0.51    inference(avatar_component_clause,[],[f216])).
% 0.20/0.51  fof(f219,plain,(
% 0.20/0.51    spl4_25 | ~spl4_24),
% 0.20/0.51    inference(avatar_split_clause,[],[f206,f200,f216])).
% 0.20/0.51  fof(f200,plain,(
% 0.20/0.51    spl4_24 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.51  fof(f206,plain,(
% 0.20/0.51    v4_relat_1(sK2,k1_relat_1(sK2)) | ~spl4_24),
% 0.20/0.51    inference(resolution,[],[f202,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.51  fof(f202,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) | ~spl4_24),
% 0.20/0.51    inference(avatar_component_clause,[],[f200])).
% 0.20/0.51  fof(f203,plain,(
% 0.20/0.51    spl4_24 | ~spl4_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f198,f89,f200])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    spl4_5 <=> sP3(sK2,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) | ~spl4_5),
% 0.20/0.51    inference(resolution,[],[f102,f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    sP3(sK2,sK0) | ~spl4_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f89])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~sP3(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))) )),
% 0.20/0.51    inference(resolution,[],[f56,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(flattening,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X2,X3,X1] : (~r1_tarski(k1_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~sP3(X3,X2)) )),
% 0.20/0.51    inference(general_splitting,[],[f52,f55_D])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | sP3(X3,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f55_D])).
% 0.20/0.51  fof(f55_D,plain,(
% 0.20/0.51    ( ! [X2,X3] : (( ! [X0] : ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) <=> ~sP3(X3,X2)) )),
% 0.20/0.51    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.51    inference(flattening,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.20/0.51  fof(f197,plain,(
% 0.20/0.51    ~spl4_23 | ~spl4_18 | spl4_22),
% 0.20/0.51    inference(avatar_split_clause,[],[f192,f188,f162,f194])).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    spl4_22 <=> k2_relat_1(sK2) = k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.51  fof(f192,plain,(
% 0.20/0.51    k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2)) | (~spl4_18 | spl4_22)),
% 0.20/0.51    inference(superposition,[],[f190,f163])).
% 0.20/0.51  fof(f190,plain,(
% 0.20/0.51    k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2)) | spl4_22),
% 0.20/0.51    inference(avatar_component_clause,[],[f188])).
% 0.20/0.51  fof(f191,plain,(
% 0.20/0.51    ~spl4_22 | ~spl4_1 | ~spl4_8 | ~spl4_14 | spl4_16),
% 0.20/0.51    inference(avatar_split_clause,[],[f181,f151,f143,f111,f58,f188])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    spl4_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    spl4_16 <=> k2_relat_1(sK2) = k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.51  fof(f181,plain,(
% 0.20/0.51    k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2)) | (~spl4_1 | ~spl4_8 | ~spl4_14 | spl4_16)),
% 0.20/0.51    inference(backward_demodulation,[],[f153,f180])).
% 0.20/0.51  fof(f180,plain,(
% 0.20/0.51    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) | (~spl4_1 | ~spl4_8 | ~spl4_14)),
% 0.20/0.51    inference(forward_demodulation,[],[f179,f113])).
% 0.20/0.51  fof(f179,plain,(
% 0.20/0.51    k1_relset_1(sK1,sK0,sK2) = k10_relat_1(sK2,sK0) | (~spl4_1 | ~spl4_14)),
% 0.20/0.51    inference(forward_demodulation,[],[f115,f144])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    k1_relset_1(sK1,sK0,sK2) = k8_relset_1(sK1,sK0,sK2,sK0) | ~spl4_1),
% 0.20/0.51    inference(resolution,[],[f49,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f58])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) | spl4_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f151])).
% 0.20/0.51  fof(f164,plain,(
% 0.20/0.51    spl4_18 | ~spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f108,f58,f162])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    ( ! [X0] : (k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0)) ) | ~spl4_1),
% 0.20/0.51    inference(resolution,[],[f51,f60])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.51  fof(f160,plain,(
% 0.20/0.51    spl4_17 | ~spl4_6 | ~spl4_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f155,f147,f98,f157])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    spl4_6 <=> sK2 = k7_relat_1(sK2,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.51  fof(f155,plain,(
% 0.20/0.51    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) | (~spl4_6 | ~spl4_15)),
% 0.20/0.51    inference(superposition,[],[f148,f100])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    sK2 = k7_relat_1(sK2,sK1) | ~spl4_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f98])).
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    ~spl4_16 | ~spl4_1 | spl4_12),
% 0.20/0.51    inference(avatar_split_clause,[],[f141,f132,f58,f151])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    spl4_12 <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) = k2_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) | (~spl4_1 | spl4_12)),
% 0.20/0.51    inference(backward_demodulation,[],[f134,f103])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    ( ! [X0] : (k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0)) ) | ~spl4_1),
% 0.20/0.51    inference(resolution,[],[f50,f60])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) | spl4_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f132])).
% 0.20/0.51  fof(f149,plain,(
% 0.20/0.51    spl4_15 | ~spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f87,f66,f147])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X3] : (k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3)) ) | ~spl4_2),
% 0.20/0.51    inference(resolution,[],[f39,f68])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    spl4_14 | ~spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f103,f58,f143])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    spl4_13 | ~spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f71,f66,f137])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) | ~spl4_2),
% 0.20/0.51    inference(resolution,[],[f68,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    ~spl4_12 | ~spl4_9 | spl4_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f130,f122,f117,f132])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    spl4_9 <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    spl4_10 <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) = k2_relset_1(sK1,sK0,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) | (~spl4_9 | spl4_10)),
% 0.20/0.51    inference(backward_demodulation,[],[f124,f119])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) | ~spl4_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f117])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) | spl4_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f122])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    ~spl4_10 | ~spl4_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f35,f126,f122])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    (k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f30])).
% 0.20/0.51  % (32551)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.51    inference(ennf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.20/0.51    inference(negated_conjecture,[],[f14])).
% 0.20/0.51  fof(f14,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    spl4_9 | ~spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f96,f58,f117])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) | ~spl4_1),
% 0.20/0.51    inference(resolution,[],[f45,f60])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    spl4_8 | ~spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f95,f58,f111])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl4_1),
% 0.20/0.51    inference(resolution,[],[f44,f60])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    spl4_6 | ~spl4_2 | ~spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f94,f75,f66,f98])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    spl4_3 <=> v4_relat_1(sK2,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    sK2 = k7_relat_1(sK2,sK1) | (~spl4_2 | ~spl4_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f93,f68])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    sK2 = k7_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | ~spl4_3),
% 0.20/0.51    inference(resolution,[],[f40,f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    v4_relat_1(sK2,sK1) | ~spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f75])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    spl4_5 | ~spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f80,f58,f89])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    sP3(sK2,sK0) | ~spl4_1),
% 0.20/0.51    inference(resolution,[],[f55,f60])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    spl4_3 | ~spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f73,f58,f75])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    v4_relat_1(sK2,sK1) | ~spl4_1),
% 0.20/0.51    inference(resolution,[],[f46,f60])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    spl4_2 | ~spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f63,f58,f66])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    v1_relat_1(sK2) | ~spl4_1),
% 0.20/0.51    inference(resolution,[],[f62,f60])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.20/0.51    inference(resolution,[],[f37,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f34,f58])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (32534)------------------------------
% 0.20/0.51  % (32534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (32534)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (32534)Memory used [KB]: 6268
% 0.20/0.51  % (32534)Time elapsed: 0.101 s
% 0.20/0.51  % (32534)------------------------------
% 0.20/0.51  % (32534)------------------------------
% 0.20/0.51  % (32545)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (32556)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (32529)Success in time 0.157 s
%------------------------------------------------------------------------------
