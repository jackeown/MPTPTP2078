%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:28 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 212 expanded)
%              Number of leaves         :   32 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :  332 ( 520 expanded)
%              Number of equality atoms :   63 (  95 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f422,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f81,f91,f95,f101,f105,f115,f125,f144,f155,f183,f210,f226,f248,f271,f272,f418,f421])).

fof(f421,plain,
    ( ~ spl4_4
    | ~ spl4_27
    | spl4_39 ),
    inference(avatar_contradiction_clause,[],[f420])).

fof(f420,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_27
    | spl4_39 ),
    inference(subsumption_resolution,[],[f419,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f419,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | ~ spl4_4
    | ~ spl4_27
    | spl4_39 ),
    inference(forward_demodulation,[],[f417,f307])).

fof(f307,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl4_4
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f306,f52])).

fof(f52,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f306,plain,
    ( ! [X0] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)
    | ~ spl4_4
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f305,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f305,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,X0))
        | k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) )
    | ~ spl4_4
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f289,f52])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k9_relat_1(k1_xboole_0,X0))
        | k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) )
    | ~ spl4_4
    | ~ spl4_27 ),
    inference(superposition,[],[f126,f270])).

fof(f270,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl4_27
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),k9_relat_1(sK3,X0))
        | k2_relat_1(sK3) = k9_relat_1(sK3,X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f97,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f97,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
    | ~ spl4_4 ),
    inference(resolution,[],[f90,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f90,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f417,plain,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f416])).

fof(f416,plain,
    ( spl4_39
  <=> r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f418,plain,
    ( ~ spl4_39
    | spl4_6
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f285,f269,f99,f416])).

fof(f99,plain,
    ( spl4_6
  <=> r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f285,plain,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | spl4_6
    | ~ spl4_27 ),
    inference(superposition,[],[f100,f270])).

fof(f100,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f272,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | sK3 != k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))
    | sK3 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f271,plain,
    ( spl4_27
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f267,f252,f269])).

fof(f252,plain,
    ( spl4_25
  <=> sK3 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f267,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f253,f67])).

fof(f67,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f253,plain,
    ( sK3 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f252])).

fof(f248,plain,
    ( ~ spl4_4
    | spl4_6
    | ~ spl4_24 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | ~ spl4_4
    | spl4_6
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f242,f97])).

fof(f242,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | spl4_6
    | ~ spl4_24 ),
    inference(superposition,[],[f100,f209])).

fof(f209,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl4_24
  <=> k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f226,plain,
    ( ~ spl4_14
    | spl4_20 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl4_14
    | spl4_20 ),
    inference(subsumption_resolution,[],[f224,f45])).

fof(f224,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl4_14
    | spl4_20 ),
    inference(forward_demodulation,[],[f223,f67])).

fof(f223,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)),sK3)
    | ~ spl4_14
    | spl4_20 ),
    inference(superposition,[],[f182,f151])).

fof(f151,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl4_14
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f182,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl4_20
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f210,plain,
    ( spl4_24
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f206,f153,f79,f69,f208])).

fof(f69,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f79,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f153,plain,
    ( spl4_15
  <=> k1_tarski(sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f206,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(equality_resolution,[],[f163])).

% (12453)Refutation not found, incomplete strategy% (12453)------------------------------
% (12453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12453)Termination reason: Refutation not found, incomplete strategy

% (12453)Memory used [KB]: 1791
% (12453)Time elapsed: 0.122 s
% (12453)------------------------------
% (12453)------------------------------
fof(f163,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK0)
        | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) )
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(superposition,[],[f86,f154])).

fof(f154,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f153])).

fof(f86,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_relat_1(sK3)
        | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) )
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f73,f83])).

fof(f83,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(resolution,[],[f80,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f80,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3)
        | k1_tarski(X0) != k1_relat_1(sK3)
        | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f70,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f70,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f183,plain,
    ( spl4_19
    | ~ spl4_20
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f146,f142,f181,f178])).

fof(f178,plain,
    ( spl4_19
  <=> sK3 = k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f142,plain,
    ( spl4_13
  <=> r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f146,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3)
    | sK3 = k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ spl4_13 ),
    inference(resolution,[],[f143,f44])).

fof(f143,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f142])).

fof(f155,plain,
    ( spl4_14
    | spl4_15
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f119,f113,f153,f150])).

fof(f113,plain,
    ( spl4_9
  <=> r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f119,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_9 ),
    inference(resolution,[],[f114,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f114,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f144,plain,
    ( spl4_13
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f131,f123,f142])).

fof(f123,plain,
    ( spl4_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f131,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | ~ spl4_10 ),
    inference(resolution,[],[f124,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f124,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f125,plain,
    ( spl4_10
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f87,f79,f69,f123])).

fof(f87,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f72,f83])).

fof(f72,plain,
    ( ~ v1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl4_1 ),
    inference(resolution,[],[f70,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f115,plain,
    ( spl4_9
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f107,f103,f89,f113])).

fof(f103,plain,
    ( spl4_7
  <=> v4_relat_1(sK3,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f107,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f106,f90])).

fof(f106,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))
    | ~ v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f104,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f104,plain,
    ( v4_relat_1(sK3,k1_tarski(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f105,plain,
    ( spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f82,f79,f103])).

fof(f82,plain,
    ( v4_relat_1(sK3,k1_tarski(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f80,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f101,plain,
    ( ~ spl4_6
    | ~ spl4_3
    | spl4_5 ),
    inference(avatar_split_clause,[],[f96,f93,f79,f99])).

fof(f93,plain,
    ( spl4_5
  <=> r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f96,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | ~ spl4_3
    | spl4_5 ),
    inference(forward_demodulation,[],[f94,f84])).

fof(f84,plain,
    ( ! [X0] : k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl4_3 ),
    inference(resolution,[],[f80,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f94,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f95,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f36,f93])).

fof(f36,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f91,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f83,f79,f89])).

fof(f81,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f34,f79])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f33,f69])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n023.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 16:57:21 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.18/0.47  % (12457)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.18/0.49  % (12478)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.18/0.49  % (12465)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.18/0.50  % (12460)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.18/0.51  % (12478)Refutation found. Thanks to Tanya!
% 0.18/0.51  % SZS status Theorem for theBenchmark
% 0.18/0.51  % (12467)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.18/0.51  % (12452)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.18/0.51  % (12454)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.18/0.51  % (12455)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.18/0.51  % (12453)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.18/0.51  % SZS output start Proof for theBenchmark
% 0.18/0.51  fof(f422,plain,(
% 0.18/0.51    $false),
% 0.18/0.51    inference(avatar_sat_refutation,[],[f71,f81,f91,f95,f101,f105,f115,f125,f144,f155,f183,f210,f226,f248,f271,f272,f418,f421])).
% 0.18/0.51  fof(f421,plain,(
% 0.18/0.51    ~spl4_4 | ~spl4_27 | spl4_39),
% 0.18/0.51    inference(avatar_contradiction_clause,[],[f420])).
% 0.18/0.51  fof(f420,plain,(
% 0.18/0.51    $false | (~spl4_4 | ~spl4_27 | spl4_39)),
% 0.18/0.51    inference(subsumption_resolution,[],[f419,f63])).
% 0.18/0.51  fof(f63,plain,(
% 0.18/0.51    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 0.18/0.51    inference(equality_resolution,[],[f40])).
% 0.18/0.51  fof(f40,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f5])).
% 0.18/0.51  fof(f5,axiom,(
% 0.18/0.51    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.18/0.51  fof(f419,plain,(
% 0.18/0.51    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | (~spl4_4 | ~spl4_27 | spl4_39)),
% 0.18/0.51    inference(forward_demodulation,[],[f417,f307])).
% 0.18/0.51  fof(f307,plain,(
% 0.18/0.51    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | (~spl4_4 | ~spl4_27)),
% 0.18/0.51    inference(forward_demodulation,[],[f306,f52])).
% 0.18/0.51  fof(f52,plain,(
% 0.18/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.18/0.51    inference(cnf_transformation,[],[f11])).
% 0.18/0.51  fof(f11,axiom,(
% 0.18/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.18/0.51  fof(f306,plain,(
% 0.18/0.51    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) ) | (~spl4_4 | ~spl4_27)),
% 0.18/0.51    inference(subsumption_resolution,[],[f305,f45])).
% 0.18/0.51  fof(f45,plain,(
% 0.18/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f2])).
% 0.18/0.51  fof(f2,axiom,(
% 0.18/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.18/0.51  fof(f305,plain,(
% 0.18/0.51    ( ! [X0] : (~r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) | k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) ) | (~spl4_4 | ~spl4_27)),
% 0.18/0.51    inference(forward_demodulation,[],[f289,f52])).
% 0.18/0.51  fof(f289,plain,(
% 0.18/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(k1_xboole_0),k9_relat_1(k1_xboole_0,X0)) | k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) ) | (~spl4_4 | ~spl4_27)),
% 0.18/0.51    inference(superposition,[],[f126,f270])).
% 0.18/0.51  fof(f270,plain,(
% 0.18/0.51    k1_xboole_0 = sK3 | ~spl4_27),
% 0.18/0.51    inference(avatar_component_clause,[],[f269])).
% 0.18/0.51  fof(f269,plain,(
% 0.18/0.51    spl4_27 <=> k1_xboole_0 = sK3),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.18/0.51  fof(f126,plain,(
% 0.18/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),k9_relat_1(sK3,X0)) | k2_relat_1(sK3) = k9_relat_1(sK3,X0)) ) | ~spl4_4),
% 0.18/0.51    inference(resolution,[],[f97,f44])).
% 0.18/0.51  fof(f44,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.18/0.51    inference(cnf_transformation,[],[f1])).
% 0.18/0.51  fof(f1,axiom,(
% 0.18/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.18/0.51  fof(f97,plain,(
% 0.18/0.51    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))) ) | ~spl4_4),
% 0.18/0.51    inference(resolution,[],[f90,f57])).
% 0.18/0.51  fof(f57,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f30])).
% 0.18/0.51  fof(f30,plain,(
% 0.18/0.51    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.18/0.51    inference(ennf_transformation,[],[f10])).
% 0.18/0.51  fof(f10,axiom,(
% 0.18/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 0.18/0.51  fof(f90,plain,(
% 0.18/0.51    v1_relat_1(sK3) | ~spl4_4),
% 0.18/0.51    inference(avatar_component_clause,[],[f89])).
% 0.18/0.51  fof(f89,plain,(
% 0.18/0.51    spl4_4 <=> v1_relat_1(sK3)),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.18/0.51  fof(f417,plain,(
% 0.18/0.51    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | spl4_39),
% 0.18/0.51    inference(avatar_component_clause,[],[f416])).
% 0.18/0.51  fof(f416,plain,(
% 0.18/0.51    spl4_39 <=> r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.18/0.51  fof(f418,plain,(
% 0.18/0.51    ~spl4_39 | spl4_6 | ~spl4_27),
% 0.18/0.51    inference(avatar_split_clause,[],[f285,f269,f99,f416])).
% 0.18/0.51  fof(f99,plain,(
% 0.18/0.51    spl4_6 <=> r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.18/0.51  fof(f285,plain,(
% 0.18/0.51    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | (spl4_6 | ~spl4_27)),
% 0.18/0.51    inference(superposition,[],[f100,f270])).
% 0.18/0.51  fof(f100,plain,(
% 0.18/0.51    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | spl4_6),
% 0.18/0.51    inference(avatar_component_clause,[],[f99])).
% 0.18/0.51  fof(f272,plain,(
% 0.18/0.51    k1_xboole_0 != k1_relat_1(sK3) | sK3 != k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)) | sK3 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))),
% 0.18/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.18/0.51  fof(f271,plain,(
% 0.18/0.51    spl4_27 | ~spl4_25),
% 0.18/0.51    inference(avatar_split_clause,[],[f267,f252,f269])).
% 0.18/0.51  fof(f252,plain,(
% 0.18/0.51    spl4_25 <=> sK3 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.18/0.51  fof(f267,plain,(
% 0.18/0.51    k1_xboole_0 = sK3 | ~spl4_25),
% 0.18/0.51    inference(forward_demodulation,[],[f253,f67])).
% 0.18/0.51  fof(f67,plain,(
% 0.18/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.18/0.51    inference(equality_resolution,[],[f49])).
% 0.18/0.51  fof(f49,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f6])).
% 0.18/0.51  fof(f6,axiom,(
% 0.18/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.18/0.51  fof(f253,plain,(
% 0.18/0.51    sK3 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)) | ~spl4_25),
% 0.18/0.51    inference(avatar_component_clause,[],[f252])).
% 0.18/0.51  fof(f248,plain,(
% 0.18/0.51    ~spl4_4 | spl4_6 | ~spl4_24),
% 0.18/0.51    inference(avatar_contradiction_clause,[],[f247])).
% 0.18/0.51  fof(f247,plain,(
% 0.18/0.51    $false | (~spl4_4 | spl4_6 | ~spl4_24)),
% 0.18/0.51    inference(subsumption_resolution,[],[f242,f97])).
% 0.18/0.51  fof(f242,plain,(
% 0.18/0.51    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | (spl4_6 | ~spl4_24)),
% 0.18/0.51    inference(superposition,[],[f100,f209])).
% 0.18/0.51  fof(f209,plain,(
% 0.18/0.51    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_24),
% 0.18/0.51    inference(avatar_component_clause,[],[f208])).
% 0.18/0.51  fof(f208,plain,(
% 0.18/0.51    spl4_24 <=> k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.18/0.51  fof(f226,plain,(
% 0.18/0.51    ~spl4_14 | spl4_20),
% 0.18/0.51    inference(avatar_contradiction_clause,[],[f225])).
% 0.18/0.51  fof(f225,plain,(
% 0.18/0.51    $false | (~spl4_14 | spl4_20)),
% 0.18/0.51    inference(subsumption_resolution,[],[f224,f45])).
% 0.18/0.51  fof(f224,plain,(
% 0.18/0.51    ~r1_tarski(k1_xboole_0,sK3) | (~spl4_14 | spl4_20)),
% 0.18/0.51    inference(forward_demodulation,[],[f223,f67])).
% 0.18/0.51  fof(f223,plain,(
% 0.18/0.51    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)),sK3) | (~spl4_14 | spl4_20)),
% 0.18/0.51    inference(superposition,[],[f182,f151])).
% 0.18/0.51  fof(f151,plain,(
% 0.18/0.51    k1_xboole_0 = k1_relat_1(sK3) | ~spl4_14),
% 0.18/0.51    inference(avatar_component_clause,[],[f150])).
% 0.18/0.51  fof(f150,plain,(
% 0.18/0.51    spl4_14 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.18/0.51  fof(f182,plain,(
% 0.18/0.51    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3) | spl4_20),
% 0.18/0.51    inference(avatar_component_clause,[],[f181])).
% 0.18/0.51  fof(f181,plain,(
% 0.18/0.51    spl4_20 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3)),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.18/0.51  fof(f210,plain,(
% 0.18/0.51    spl4_24 | ~spl4_1 | ~spl4_3 | ~spl4_15),
% 0.18/0.51    inference(avatar_split_clause,[],[f206,f153,f79,f69,f208])).
% 0.18/0.51  fof(f69,plain,(
% 0.18/0.51    spl4_1 <=> v1_funct_1(sK3)),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.18/0.51  fof(f79,plain,(
% 0.18/0.51    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.18/0.51  fof(f153,plain,(
% 0.18/0.51    spl4_15 <=> k1_tarski(sK0) = k1_relat_1(sK3)),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.18/0.51  fof(f206,plain,(
% 0.18/0.51    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_15)),
% 0.18/0.51    inference(equality_resolution,[],[f163])).
% 0.18/0.51  % (12453)Refutation not found, incomplete strategy% (12453)------------------------------
% 0.18/0.51  % (12453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (12453)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  
% 0.18/0.51  % (12453)Memory used [KB]: 1791
% 0.18/0.51  % (12453)Time elapsed: 0.122 s
% 0.18/0.51  % (12453)------------------------------
% 0.18/0.51  % (12453)------------------------------
% 0.18/0.51  fof(f163,plain,(
% 0.18/0.51    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) ) | (~spl4_1 | ~spl4_3 | ~spl4_15)),
% 0.18/0.51    inference(superposition,[],[f86,f154])).
% 0.18/0.51  fof(f154,plain,(
% 0.18/0.51    k1_tarski(sK0) = k1_relat_1(sK3) | ~spl4_15),
% 0.18/0.51    inference(avatar_component_clause,[],[f153])).
% 0.18/0.51  fof(f86,plain,(
% 0.18/0.51    ( ! [X0] : (k1_tarski(X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) ) | (~spl4_1 | ~spl4_3)),
% 0.18/0.51    inference(subsumption_resolution,[],[f73,f83])).
% 0.18/0.51  fof(f83,plain,(
% 0.18/0.51    v1_relat_1(sK3) | ~spl4_3),
% 0.18/0.51    inference(resolution,[],[f80,f53])).
% 0.18/0.51  fof(f53,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f27])).
% 0.18/0.51  fof(f27,plain,(
% 0.18/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.51    inference(ennf_transformation,[],[f13])).
% 0.18/0.51  fof(f13,axiom,(
% 0.18/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.18/0.51  fof(f80,plain,(
% 0.18/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~spl4_3),
% 0.18/0.51    inference(avatar_component_clause,[],[f79])).
% 0.18/0.51  fof(f73,plain,(
% 0.18/0.51    ( ! [X0] : (~v1_relat_1(sK3) | k1_tarski(X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) ) | ~spl4_1),
% 0.18/0.51    inference(resolution,[],[f70,f46])).
% 0.18/0.51  fof(f46,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f25])).
% 0.18/0.51  fof(f25,plain,(
% 0.18/0.51    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.18/0.51    inference(flattening,[],[f24])).
% 0.18/0.51  fof(f24,plain,(
% 0.18/0.51    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.18/0.51    inference(ennf_transformation,[],[f12])).
% 0.18/0.51  fof(f12,axiom,(
% 0.18/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.18/0.51  fof(f70,plain,(
% 0.18/0.51    v1_funct_1(sK3) | ~spl4_1),
% 0.18/0.51    inference(avatar_component_clause,[],[f69])).
% 0.18/0.51  fof(f183,plain,(
% 0.18/0.51    spl4_19 | ~spl4_20 | ~spl4_13),
% 0.18/0.51    inference(avatar_split_clause,[],[f146,f142,f181,f178])).
% 0.18/0.51  fof(f178,plain,(
% 0.18/0.51    spl4_19 <=> sK3 = k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.18/0.51  fof(f142,plain,(
% 0.18/0.51    spl4_13 <=> r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.18/0.51  fof(f146,plain,(
% 0.18/0.51    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3) | sK3 = k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)) | ~spl4_13),
% 0.18/0.51    inference(resolution,[],[f143,f44])).
% 0.18/0.51  fof(f143,plain,(
% 0.18/0.51    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) | ~spl4_13),
% 0.18/0.51    inference(avatar_component_clause,[],[f142])).
% 0.18/0.51  fof(f155,plain,(
% 0.18/0.51    spl4_14 | spl4_15 | ~spl4_9),
% 0.18/0.51    inference(avatar_split_clause,[],[f119,f113,f153,f150])).
% 0.18/0.51  fof(f113,plain,(
% 0.18/0.51    spl4_9 <=> r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.18/0.51  fof(f119,plain,(
% 0.18/0.51    k1_tarski(sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3) | ~spl4_9),
% 0.18/0.51    inference(resolution,[],[f114,f39])).
% 0.18/0.51  fof(f39,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0) )),
% 0.18/0.51    inference(cnf_transformation,[],[f5])).
% 0.18/0.51  fof(f114,plain,(
% 0.18/0.51    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) | ~spl4_9),
% 0.18/0.51    inference(avatar_component_clause,[],[f113])).
% 0.18/0.51  fof(f144,plain,(
% 0.18/0.51    spl4_13 | ~spl4_10),
% 0.18/0.51    inference(avatar_split_clause,[],[f131,f123,f142])).
% 0.18/0.51  fof(f123,plain,(
% 0.18/0.51    spl4_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.18/0.51  fof(f131,plain,(
% 0.18/0.51    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) | ~spl4_10),
% 0.18/0.51    inference(resolution,[],[f124,f38])).
% 0.18/0.51  fof(f38,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f7])).
% 0.18/0.51  fof(f7,axiom,(
% 0.18/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.18/0.51  fof(f124,plain,(
% 0.18/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~spl4_10),
% 0.18/0.51    inference(avatar_component_clause,[],[f123])).
% 0.18/0.51  fof(f125,plain,(
% 0.18/0.51    spl4_10 | ~spl4_1 | ~spl4_3),
% 0.18/0.51    inference(avatar_split_clause,[],[f87,f79,f69,f123])).
% 0.18/0.51  fof(f87,plain,(
% 0.18/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | (~spl4_1 | ~spl4_3)),
% 0.18/0.51    inference(subsumption_resolution,[],[f72,f83])).
% 0.18/0.51  fof(f72,plain,(
% 0.18/0.51    ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~spl4_1),
% 0.18/0.51    inference(resolution,[],[f70,f55])).
% 0.18/0.51  fof(f55,plain,(
% 0.18/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f29])).
% 0.18/0.51  fof(f29,plain,(
% 0.18/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.51    inference(flattening,[],[f28])).
% 0.18/0.51  fof(f28,plain,(
% 0.18/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.18/0.51    inference(ennf_transformation,[],[f20])).
% 0.18/0.51  fof(f20,plain,(
% 0.18/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)))),
% 0.18/0.51    inference(pure_predicate_removal,[],[f16])).
% 0.18/0.51  fof(f16,axiom,(
% 0.18/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.18/0.51  fof(f115,plain,(
% 0.18/0.51    spl4_9 | ~spl4_4 | ~spl4_7),
% 0.18/0.51    inference(avatar_split_clause,[],[f107,f103,f89,f113])).
% 0.18/0.51  fof(f103,plain,(
% 0.18/0.51    spl4_7 <=> v4_relat_1(sK3,k1_tarski(sK0))),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.18/0.51  fof(f107,plain,(
% 0.18/0.51    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) | (~spl4_4 | ~spl4_7)),
% 0.18/0.51    inference(subsumption_resolution,[],[f106,f90])).
% 0.18/0.51  fof(f106,plain,(
% 0.18/0.51    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) | ~v1_relat_1(sK3) | ~spl4_7),
% 0.18/0.51    inference(resolution,[],[f104,f59])).
% 0.18/0.51  fof(f59,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f31])).
% 0.18/0.51  fof(f31,plain,(
% 0.18/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.18/0.51    inference(ennf_transformation,[],[f8])).
% 0.18/0.51  fof(f8,axiom,(
% 0.18/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.18/0.51  fof(f104,plain,(
% 0.18/0.51    v4_relat_1(sK3,k1_tarski(sK0)) | ~spl4_7),
% 0.18/0.51    inference(avatar_component_clause,[],[f103])).
% 0.18/0.51  fof(f105,plain,(
% 0.18/0.51    spl4_7 | ~spl4_3),
% 0.18/0.51    inference(avatar_split_clause,[],[f82,f79,f103])).
% 0.18/0.51  fof(f82,plain,(
% 0.18/0.51    v4_relat_1(sK3,k1_tarski(sK0)) | ~spl4_3),
% 0.18/0.51    inference(resolution,[],[f80,f61])).
% 0.18/0.51  fof(f61,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f32])).
% 0.18/0.51  fof(f32,plain,(
% 0.18/0.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.51    inference(ennf_transformation,[],[f21])).
% 0.18/0.51  fof(f21,plain,(
% 0.18/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.18/0.51    inference(pure_predicate_removal,[],[f14])).
% 0.18/0.51  fof(f14,axiom,(
% 0.18/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.18/0.51  fof(f101,plain,(
% 0.18/0.51    ~spl4_6 | ~spl4_3 | spl4_5),
% 0.18/0.51    inference(avatar_split_clause,[],[f96,f93,f79,f99])).
% 0.18/0.51  fof(f93,plain,(
% 0.18/0.51    spl4_5 <=> r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.18/0.51  fof(f96,plain,(
% 0.18/0.51    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | (~spl4_3 | spl4_5)),
% 0.18/0.51    inference(forward_demodulation,[],[f94,f84])).
% 0.18/0.51  fof(f84,plain,(
% 0.18/0.51    ( ! [X0] : (k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl4_3),
% 0.18/0.51    inference(resolution,[],[f80,f47])).
% 0.18/0.51  fof(f47,plain,(
% 0.18/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f26])).
% 0.18/0.51  fof(f26,plain,(
% 0.18/0.51    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.51    inference(ennf_transformation,[],[f15])).
% 0.18/0.51  fof(f15,axiom,(
% 0.18/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.18/0.51  fof(f94,plain,(
% 0.18/0.51    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | spl4_5),
% 0.18/0.51    inference(avatar_component_clause,[],[f93])).
% 0.18/0.51  fof(f95,plain,(
% 0.18/0.51    ~spl4_5),
% 0.18/0.51    inference(avatar_split_clause,[],[f36,f93])).
% 0.18/0.51  fof(f36,plain,(
% 0.18/0.51    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.18/0.51    inference(cnf_transformation,[],[f23])).
% 0.18/0.51  fof(f23,plain,(
% 0.18/0.51    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 0.18/0.51    inference(flattening,[],[f22])).
% 0.18/0.51  fof(f22,plain,(
% 0.18/0.51    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 0.18/0.51    inference(ennf_transformation,[],[f19])).
% 0.18/0.51  fof(f19,plain,(
% 0.18/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.18/0.51    inference(pure_predicate_removal,[],[f18])).
% 0.18/0.51  fof(f18,negated_conjecture,(
% 0.18/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.18/0.51    inference(negated_conjecture,[],[f17])).
% 0.18/0.51  fof(f17,conjecture,(
% 0.18/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 0.18/0.51  fof(f91,plain,(
% 0.18/0.51    spl4_4 | ~spl4_3),
% 0.18/0.51    inference(avatar_split_clause,[],[f83,f79,f89])).
% 0.18/0.51  fof(f81,plain,(
% 0.18/0.51    spl4_3),
% 0.18/0.51    inference(avatar_split_clause,[],[f34,f79])).
% 0.18/0.51  fof(f34,plain,(
% 0.18/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.18/0.51    inference(cnf_transformation,[],[f23])).
% 0.18/0.51  fof(f71,plain,(
% 0.18/0.51    spl4_1),
% 0.18/0.51    inference(avatar_split_clause,[],[f33,f69])).
% 0.18/0.51  fof(f33,plain,(
% 0.18/0.51    v1_funct_1(sK3)),
% 0.18/0.51    inference(cnf_transformation,[],[f23])).
% 0.18/0.51  % SZS output end Proof for theBenchmark
% 0.18/0.51  % (12478)------------------------------
% 0.18/0.51  % (12478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (12478)Termination reason: Refutation
% 0.18/0.51  
% 0.18/0.51  % (12478)Memory used [KB]: 6524
% 0.18/0.51  % (12478)Time elapsed: 0.122 s
% 0.18/0.51  % (12478)------------------------------
% 0.18/0.51  % (12478)------------------------------
% 0.18/0.51  % (12449)Success in time 0.174 s
%------------------------------------------------------------------------------
