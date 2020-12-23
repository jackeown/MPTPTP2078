%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 209 expanded)
%              Number of leaves         :   30 (  83 expanded)
%              Depth                    :   11
%              Number of atoms          :  369 ( 733 expanded)
%              Number of equality atoms :   83 ( 171 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f302,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f74,f79,f84,f89,f94,f118,f124,f146,f152,f163,f173,f179,f186,f192,f197,f241,f263,f300])).

fof(f300,plain,
    ( spl4_20
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | spl4_20
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f292,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f292,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k10_relat_1(sK3,k9_relat_1(sK3,k1_xboole_0))))
    | spl4_20
    | ~ spl4_28 ),
    inference(backward_demodulation,[],[f185,f246])).

fof(f246,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl4_28
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f185,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl4_20
  <=> m1_subset_1(sK2,k1_zfmisc_1(k10_relat_1(sK3,k9_relat_1(sK3,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f263,plain,
    ( spl4_28
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f262,f110,f71,f244])).

fof(f71,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f110,plain,
    ( spl4_10
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f262,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f112,f73])).

fof(f73,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f112,plain,
    ( sK0 = sK2
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f241,plain,
    ( ~ spl4_3
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl4_3
    | spl4_12 ),
    inference(subsumption_resolution,[],[f208,f38])).

fof(f208,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl4_3
    | spl4_12 ),
    inference(backward_demodulation,[],[f123,f73])).

fof(f123,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK2))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl4_12
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f197,plain,
    ( spl4_16
    | spl4_2
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f164,f86,f81,f67,f154])).

fof(f154,plain,
    ( spl4_16
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f67,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f81,plain,
    ( spl4_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f86,plain,
    ( spl4_6
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f164,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f132,f88])).

fof(f88,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f132,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_5 ),
    inference(resolution,[],[f83,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f83,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f192,plain,
    ( ~ spl4_4
    | ~ spl4_7
    | ~ spl4_14
    | ~ spl4_18
    | spl4_19 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_14
    | ~ spl4_18
    | spl4_19 ),
    inference(subsumption_resolution,[],[f190,f78])).

fof(f78,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_4
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f190,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ spl4_7
    | ~ spl4_14
    | ~ spl4_18
    | spl4_19 ),
    inference(forward_demodulation,[],[f189,f171])).

fof(f171,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl4_18
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f189,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ spl4_7
    | ~ spl4_14
    | spl4_19 ),
    inference(subsumption_resolution,[],[f188,f145])).

fof(f145,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f143])).

% (5382)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
fof(f143,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f188,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_7
    | spl4_19 ),
    inference(subsumption_resolution,[],[f187,f93])).

fof(f93,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f187,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_19 ),
    inference(subsumption_resolution,[],[f181,f55])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f181,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,sK2))
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_19 ),
    inference(resolution,[],[f178,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f178,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl4_19
  <=> r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f186,plain,
    ( ~ spl4_20
    | spl4_19 ),
    inference(avatar_split_clause,[],[f180,f176,f183])).

fof(f180,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k10_relat_1(sK3,k9_relat_1(sK3,sK2))))
    | spl4_19 ),
    inference(unit_resulting_resolution,[],[f178,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f179,plain,
    ( ~ spl4_19
    | ~ spl4_5
    | spl4_15 ),
    inference(avatar_split_clause,[],[f174,f149,f81,f176])).

fof(f149,plain,
    ( spl4_15
  <=> r1_tarski(sK2,k10_relat_1(sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f174,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | ~ spl4_5
    | spl4_15 ),
    inference(forward_demodulation,[],[f151,f127])).

fof(f127,plain,
    ( ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(sK0,sK1,sK3,X0)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f83,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f151,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f149])).

fof(f173,plain,
    ( spl4_18
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f172,f159,f154,f169])).

fof(f159,plain,
    ( spl4_17
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f172,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(backward_demodulation,[],[f161,f156])).

fof(f156,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f154])).

fof(f161,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f159])).

fof(f163,plain,
    ( spl4_17
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f131,f81,f159])).

fof(f131,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_5 ),
    inference(resolution,[],[f83,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f152,plain,
    ( ~ spl4_15
    | spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f147,f81,f62,f149])).

fof(f62,plain,
    ( spl4_1
  <=> r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f147,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
    | spl4_1
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f64,f128])).

fof(f128,plain,
    ( ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f83,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f64,plain,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f146,plain,
    ( spl4_14
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f129,f81,f143])).

fof(f129,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f52,f83,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f124,plain,
    ( ~ spl4_12
    | spl4_11 ),
    inference(avatar_split_clause,[],[f119,f114,f121])).

fof(f114,plain,
    ( spl4_11
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f119,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK2))
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f116,f39])).

fof(f116,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f118,plain,
    ( spl4_10
    | ~ spl4_11
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f103,f76,f114,f110])).

fof(f103,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK0 = sK2
    | ~ spl4_4 ),
    inference(resolution,[],[f78,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f94,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f30,f91])).

fof(f30,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).

fof(f89,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f31,f86])).

fof(f31,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f32,f81])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f33,f76])).

fof(f33,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,
    ( ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f34,f71,f67])).

fof(f34,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f35,f62])).

fof(f35,plain,(
    ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (5364)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (5364)Refutation not found, incomplete strategy% (5364)------------------------------
% 0.20/0.52  % (5364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5364)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5364)Memory used [KB]: 6140
% 0.20/0.52  % (5364)Time elapsed: 0.086 s
% 0.20/0.52  % (5364)------------------------------
% 0.20/0.52  % (5364)------------------------------
% 0.20/0.52  % (5372)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (5372)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f302,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f65,f74,f79,f84,f89,f94,f118,f124,f146,f152,f163,f173,f179,f186,f192,f197,f241,f263,f300])).
% 0.20/0.53  fof(f300,plain,(
% 0.20/0.53    spl4_20 | ~spl4_28),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f299])).
% 0.20/0.53  fof(f299,plain,(
% 0.20/0.53    $false | (spl4_20 | ~spl4_28)),
% 0.20/0.53    inference(subsumption_resolution,[],[f292,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.53  fof(f292,plain,(
% 0.20/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k10_relat_1(sK3,k9_relat_1(sK3,k1_xboole_0)))) | (spl4_20 | ~spl4_28)),
% 0.20/0.53    inference(backward_demodulation,[],[f185,f246])).
% 0.20/0.53  fof(f246,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | ~spl4_28),
% 0.20/0.53    inference(avatar_component_clause,[],[f244])).
% 0.20/0.53  fof(f244,plain,(
% 0.20/0.53    spl4_28 <=> k1_xboole_0 = sK2),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.53  fof(f185,plain,(
% 0.20/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k10_relat_1(sK3,k9_relat_1(sK3,sK2)))) | spl4_20),
% 0.20/0.53    inference(avatar_component_clause,[],[f183])).
% 0.20/0.53  fof(f183,plain,(
% 0.20/0.53    spl4_20 <=> m1_subset_1(sK2,k1_zfmisc_1(k10_relat_1(sK3,k9_relat_1(sK3,sK2))))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.53  fof(f263,plain,(
% 0.20/0.53    spl4_28 | ~spl4_3 | ~spl4_10),
% 0.20/0.53    inference(avatar_split_clause,[],[f262,f110,f71,f244])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    spl4_3 <=> k1_xboole_0 = sK0),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    spl4_10 <=> sK0 = sK2),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | (~spl4_3 | ~spl4_10)),
% 0.20/0.53    inference(forward_demodulation,[],[f112,f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | ~spl4_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f71])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    sK0 = sK2 | ~spl4_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f110])).
% 0.20/0.53  fof(f241,plain,(
% 0.20/0.53    ~spl4_3 | spl4_12),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f240])).
% 0.20/0.53  fof(f240,plain,(
% 0.20/0.53    $false | (~spl4_3 | spl4_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f208,f38])).
% 0.20/0.53  fof(f208,plain,(
% 0.20/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) | (~spl4_3 | spl4_12)),
% 0.20/0.53    inference(backward_demodulation,[],[f123,f73])).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    ~m1_subset_1(sK0,k1_zfmisc_1(sK2)) | spl4_12),
% 0.20/0.53    inference(avatar_component_clause,[],[f121])).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    spl4_12 <=> m1_subset_1(sK0,k1_zfmisc_1(sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.53  fof(f197,plain,(
% 0.20/0.53    spl4_16 | spl4_2 | ~spl4_5 | ~spl4_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f164,f86,f81,f67,f154])).
% 0.20/0.53  fof(f154,plain,(
% 0.20/0.53    spl4_16 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    spl4_2 <=> k1_xboole_0 = sK1),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    spl4_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    spl4_6 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.53  fof(f164,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl4_5 | ~spl4_6)),
% 0.20/0.53    inference(subsumption_resolution,[],[f132,f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    v1_funct_2(sK3,sK0,sK1) | ~spl4_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f86])).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_5),
% 0.20/0.53    inference(resolution,[],[f83,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f81])).
% 0.20/0.53  fof(f192,plain,(
% 0.20/0.53    ~spl4_4 | ~spl4_7 | ~spl4_14 | ~spl4_18 | spl4_19),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f191])).
% 0.20/0.53  fof(f191,plain,(
% 0.20/0.53    $false | (~spl4_4 | ~spl4_7 | ~spl4_14 | ~spl4_18 | spl4_19)),
% 0.20/0.53    inference(subsumption_resolution,[],[f190,f78])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    r1_tarski(sK2,sK0) | ~spl4_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f76])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    spl4_4 <=> r1_tarski(sK2,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.53  fof(f190,plain,(
% 0.20/0.53    ~r1_tarski(sK2,sK0) | (~spl4_7 | ~spl4_14 | ~spl4_18 | spl4_19)),
% 0.20/0.53    inference(forward_demodulation,[],[f189,f171])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK3) | ~spl4_18),
% 0.20/0.53    inference(avatar_component_clause,[],[f169])).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    spl4_18 <=> sK0 = k1_relat_1(sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.53  fof(f189,plain,(
% 0.20/0.53    ~r1_tarski(sK2,k1_relat_1(sK3)) | (~spl4_7 | ~spl4_14 | spl4_19)),
% 0.20/0.53    inference(subsumption_resolution,[],[f188,f145])).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    v1_relat_1(sK3) | ~spl4_14),
% 0.20/0.53    inference(avatar_component_clause,[],[f143])).
% 0.20/0.53  % (5382)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.53  fof(f143,plain,(
% 0.20/0.53    spl4_14 <=> v1_relat_1(sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.53  fof(f188,plain,(
% 0.20/0.53    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_7 | spl4_19)),
% 0.20/0.53    inference(subsumption_resolution,[],[f187,f93])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    v1_funct_1(sK3) | ~spl4_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f91])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    spl4_7 <=> v1_funct_1(sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.53  fof(f187,plain,(
% 0.20/0.53    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_19),
% 0.20/0.53    inference(subsumption_resolution,[],[f181,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(flattening,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f181,plain,(
% 0.20/0.53    ~r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,sK2)) | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_19),
% 0.20/0.53    inference(resolution,[],[f178,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 0.20/0.53  fof(f178,plain,(
% 0.20/0.53    ~r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) | spl4_19),
% 0.20/0.53    inference(avatar_component_clause,[],[f176])).
% 0.20/0.53  fof(f176,plain,(
% 0.20/0.53    spl4_19 <=> r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.53  fof(f186,plain,(
% 0.20/0.53    ~spl4_20 | spl4_19),
% 0.20/0.53    inference(avatar_split_clause,[],[f180,f176,f183])).
% 0.20/0.53  fof(f180,plain,(
% 0.20/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k10_relat_1(sK3,k9_relat_1(sK3,sK2)))) | spl4_19),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f178,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.53  fof(f179,plain,(
% 0.20/0.53    ~spl4_19 | ~spl4_5 | spl4_15),
% 0.20/0.53    inference(avatar_split_clause,[],[f174,f149,f81,f176])).
% 0.20/0.53  fof(f149,plain,(
% 0.20/0.53    spl4_15 <=> r1_tarski(sK2,k10_relat_1(sK3,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.53  fof(f174,plain,(
% 0.20/0.53    ~r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) | (~spl4_5 | spl4_15)),
% 0.20/0.53    inference(forward_demodulation,[],[f151,f127])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(sK0,sK1,sK3,X0)) ) | ~spl4_5),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f83,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.53  fof(f151,plain,(
% 0.20/0.53    ~r1_tarski(sK2,k10_relat_1(sK3,k7_relset_1(sK0,sK1,sK3,sK2))) | spl4_15),
% 0.20/0.53    inference(avatar_component_clause,[],[f149])).
% 0.20/0.53  fof(f173,plain,(
% 0.20/0.53    spl4_18 | ~spl4_16 | ~spl4_17),
% 0.20/0.53    inference(avatar_split_clause,[],[f172,f159,f154,f169])).
% 0.20/0.53  fof(f159,plain,(
% 0.20/0.53    spl4_17 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.53  fof(f172,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK3) | (~spl4_16 | ~spl4_17)),
% 0.20/0.53    inference(backward_demodulation,[],[f161,f156])).
% 0.20/0.53  fof(f156,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_16),
% 0.20/0.53    inference(avatar_component_clause,[],[f154])).
% 0.20/0.53  fof(f161,plain,(
% 0.20/0.53    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl4_17),
% 0.20/0.53    inference(avatar_component_clause,[],[f159])).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    spl4_17 | ~spl4_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f131,f81,f159])).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl4_5),
% 0.20/0.53    inference(resolution,[],[f83,f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.53  fof(f152,plain,(
% 0.20/0.53    ~spl4_15 | spl4_1 | ~spl4_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f147,f81,f62,f149])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    spl4_1 <=> r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.53  fof(f147,plain,(
% 0.20/0.53    ~r1_tarski(sK2,k10_relat_1(sK3,k7_relset_1(sK0,sK1,sK3,sK2))) | (spl4_1 | ~spl4_5)),
% 0.20/0.53    inference(backward_demodulation,[],[f64,f128])).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    ( ! [X0] : (k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK1,sK3,X0)) ) | ~spl4_5),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f83,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) | spl4_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f62])).
% 0.20/0.53  fof(f146,plain,(
% 0.20/0.53    spl4_14 | ~spl4_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f129,f81,f143])).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    v1_relat_1(sK3) | ~spl4_5),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f52,f83,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    ~spl4_12 | spl4_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f119,f114,f121])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    spl4_11 <=> r1_tarski(sK0,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    ~m1_subset_1(sK0,k1_zfmisc_1(sK2)) | spl4_11),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f116,f39])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    ~r1_tarski(sK0,sK2) | spl4_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f114])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    spl4_10 | ~spl4_11 | ~spl4_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f103,f76,f114,f110])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    ~r1_tarski(sK0,sK2) | sK0 = sK2 | ~spl4_4),
% 0.20/0.53    inference(resolution,[],[f78,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    spl4_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f30,f91])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    v1_funct_1(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : (~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : (~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.53    inference(flattening,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.53    inference(negated_conjecture,[],[f12])).
% 0.20/0.53  fof(f12,conjecture,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    spl4_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f31,f86])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    spl4_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f32,f81])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    spl4_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f33,f76])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    r1_tarski(sK2,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ~spl4_2 | spl4_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f34,f71,f67])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ~spl4_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f35,f62])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (5372)------------------------------
% 0.20/0.53  % (5372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5372)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (5372)Memory used [KB]: 6268
% 0.20/0.53  % (5372)Time elapsed: 0.091 s
% 0.20/0.53  % (5372)------------------------------
% 0.20/0.53  % (5372)------------------------------
% 0.20/0.53  % (5358)Success in time 0.171 s
%------------------------------------------------------------------------------
