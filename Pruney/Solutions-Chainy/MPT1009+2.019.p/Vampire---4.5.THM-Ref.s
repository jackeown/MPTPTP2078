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
% DateTime   : Thu Dec  3 13:04:28 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 187 expanded)
%              Number of leaves         :   31 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :  304 ( 459 expanded)
%              Number of equality atoms :   57 (  81 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f307,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f80,f90,f94,f100,f104,f114,f124,f143,f154,f182,f209,f225,f247,f270,f271,f302])).

fof(f302,plain,
    ( spl4_6
    | ~ spl4_27 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | spl4_6
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f300,f62])).

fof(f62,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f300,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | spl4_6
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f284,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f284,plain,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | spl4_6
    | ~ spl4_27 ),
    inference(superposition,[],[f99,f269])).

fof(f269,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl4_27
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f99,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_6
  <=> r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f271,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | sK3 != k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))
    | sK3 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f270,plain,
    ( spl4_27
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f266,f251,f268])).

fof(f251,plain,
    ( spl4_25
  <=> sK3 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f266,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f252,f66])).

fof(f66,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f252,plain,
    ( sK3 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f251])).

fof(f247,plain,
    ( ~ spl4_4
    | spl4_6
    | ~ spl4_24 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | ~ spl4_4
    | spl4_6
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f241,f96])).

fof(f96,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
    | ~ spl4_4 ),
    inference(resolution,[],[f89,f55])).

fof(f55,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f89,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f241,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | spl4_6
    | ~ spl4_24 ),
    inference(superposition,[],[f99,f208])).

fof(f208,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl4_24
  <=> k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f225,plain,
    ( ~ spl4_14
    | spl4_20 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl4_14
    | spl4_20 ),
    inference(subsumption_resolution,[],[f223,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f223,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl4_14
    | spl4_20 ),
    inference(forward_demodulation,[],[f222,f66])).

fof(f222,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)),sK3)
    | ~ spl4_14
    | spl4_20 ),
    inference(superposition,[],[f181,f150])).

fof(f150,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl4_14
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f181,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl4_20
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f209,plain,
    ( spl4_24
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f205,f152,f78,f68,f207])).

fof(f68,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f78,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f152,plain,
    ( spl4_15
  <=> k1_tarski(sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f205,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(equality_resolution,[],[f162])).

fof(f162,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK0)
        | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) )
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(superposition,[],[f85,f153])).

fof(f153,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f152])).

fof(f85,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_relat_1(sK3)
        | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) )
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f72,f82])).

fof(f82,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(resolution,[],[f79,f52])).

fof(f52,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f79,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3)
        | k1_tarski(X0) != k1_relat_1(sK3)
        | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f69,f46])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f69,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f182,plain,
    ( spl4_19
    | ~ spl4_20
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f145,f141,f180,f177])).

fof(f177,plain,
    ( spl4_19
  <=> sK3 = k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f141,plain,
    ( spl4_13
  <=> r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f145,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3)
    | sK3 = k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ spl4_13 ),
    inference(resolution,[],[f142,f44])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f142,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f141])).

fof(f154,plain,
    ( spl4_14
    | spl4_15
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f118,f112,f152,f149])).

fof(f112,plain,
    ( spl4_9
  <=> r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f118,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_9 ),
    inference(resolution,[],[f113,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f113,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f143,plain,
    ( spl4_13
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f130,f122,f141])).

fof(f122,plain,
    ( spl4_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f130,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | ~ spl4_10 ),
    inference(resolution,[],[f123,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f123,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f124,plain,
    ( spl4_10
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f86,f78,f68,f122])).

fof(f86,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f71,f82])).

fof(f71,plain,
    ( ~ v1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl4_1 ),
    inference(resolution,[],[f69,f53])).

fof(f53,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f114,plain,
    ( spl4_9
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f106,f102,f88,f112])).

fof(f102,plain,
    ( spl4_7
  <=> v4_relat_1(sK3,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f106,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f105,f89])).

fof(f105,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))
    | ~ v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f103,f57])).

fof(f57,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f103,plain,
    ( v4_relat_1(sK3,k1_tarski(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f104,plain,
    ( spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f81,f78,f102])).

fof(f81,plain,
    ( v4_relat_1(sK3,k1_tarski(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f79,f59])).

fof(f59,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f100,plain,
    ( ~ spl4_6
    | ~ spl4_3
    | spl4_5 ),
    inference(avatar_split_clause,[],[f95,f92,f78,f98])).

fof(f92,plain,
    ( spl4_5
  <=> r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f95,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | ~ spl4_3
    | spl4_5 ),
    inference(forward_demodulation,[],[f93,f83])).

fof(f83,plain,
    ( ! [X0] : k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl4_3 ),
    inference(resolution,[],[f79,f47])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f93,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f94,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f36,f92])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f90,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f82,f78,f88])).

fof(f80,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f34,f78])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 19:44:51 EST 2020
% 0.22/0.36  % CPUTime    : 
% 0.23/0.52  % (6933)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.52  % (6932)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.53  % (6957)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.23/0.53  % (6940)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.53  % (6957)Refutation not found, incomplete strategy% (6957)------------------------------
% 0.23/0.53  % (6957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (6957)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (6957)Memory used [KB]: 1663
% 0.23/0.53  % (6957)Time elapsed: 0.107 s
% 0.23/0.53  % (6957)------------------------------
% 0.23/0.53  % (6957)------------------------------
% 0.23/0.53  % (6930)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.53  % (6928)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.23/0.53  % (6935)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.53  % (6954)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.23/0.54  % (6928)Refutation not found, incomplete strategy% (6928)------------------------------
% 0.23/0.54  % (6928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (6928)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (6928)Memory used [KB]: 1791
% 0.23/0.54  % (6928)Time elapsed: 0.106 s
% 0.23/0.54  % (6928)------------------------------
% 0.23/0.54  % (6928)------------------------------
% 0.23/0.54  % (6945)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.23/0.54  % (6927)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.55  % (6939)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.23/0.55  % (6929)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.55  % (6937)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.23/0.55  % (6936)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.23/0.55  % (6931)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.55  % (6950)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.55  % (6951)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.55  % (6956)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.23/0.56  % (6956)Refutation not found, incomplete strategy% (6956)------------------------------
% 0.23/0.56  % (6956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (6956)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (6956)Memory used [KB]: 10746
% 0.23/0.56  % (6956)Time elapsed: 0.130 s
% 0.23/0.56  % (6956)------------------------------
% 0.23/0.56  % (6956)------------------------------
% 0.23/0.56  % (6942)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.56  % (6943)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.56  % (6954)Refutation found. Thanks to Tanya!
% 0.23/0.56  % SZS status Theorem for theBenchmark
% 0.23/0.56  % (6945)Refutation not found, incomplete strategy% (6945)------------------------------
% 0.23/0.56  % (6945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (6945)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (6945)Memory used [KB]: 1791
% 0.23/0.56  % (6945)Time elapsed: 0.124 s
% 0.23/0.56  % (6945)------------------------------
% 0.23/0.56  % (6945)------------------------------
% 0.23/0.56  % (6947)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.23/0.56  % (6943)Refutation not found, incomplete strategy% (6943)------------------------------
% 0.23/0.56  % (6943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (6937)Refutation not found, incomplete strategy% (6937)------------------------------
% 0.23/0.56  % (6937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (6937)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (6937)Memory used [KB]: 10746
% 0.23/0.56  % (6937)Time elapsed: 0.135 s
% 0.23/0.56  % (6937)------------------------------
% 0.23/0.56  % (6937)------------------------------
% 0.23/0.56  % (6946)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.39/0.56  % SZS output start Proof for theBenchmark
% 1.39/0.56  fof(f307,plain,(
% 1.39/0.56    $false),
% 1.39/0.56    inference(avatar_sat_refutation,[],[f70,f80,f90,f94,f100,f104,f114,f124,f143,f154,f182,f209,f225,f247,f270,f271,f302])).
% 1.39/0.56  fof(f302,plain,(
% 1.39/0.56    spl4_6 | ~spl4_27),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f301])).
% 1.39/0.56  fof(f301,plain,(
% 1.39/0.56    $false | (spl4_6 | ~spl4_27)),
% 1.39/0.56    inference(subsumption_resolution,[],[f300,f62])).
% 1.39/0.56  fof(f62,plain,(
% 1.39/0.56    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 1.39/0.56    inference(equality_resolution,[],[f40])).
% 1.39/0.56  fof(f40,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f6])).
% 1.39/0.56  fof(f6,axiom,(
% 1.39/0.56    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.39/0.56  fof(f300,plain,(
% 1.39/0.56    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | (spl4_6 | ~spl4_27)),
% 1.39/0.56    inference(forward_demodulation,[],[f284,f51])).
% 1.39/0.56  fof(f51,plain,(
% 1.39/0.56    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f11])).
% 1.39/0.56  fof(f11,axiom,(
% 1.39/0.56    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 1.39/0.56  fof(f284,plain,(
% 1.39/0.56    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | (spl4_6 | ~spl4_27)),
% 1.39/0.56    inference(superposition,[],[f99,f269])).
% 1.39/0.56  fof(f269,plain,(
% 1.39/0.56    k1_xboole_0 = sK3 | ~spl4_27),
% 1.39/0.56    inference(avatar_component_clause,[],[f268])).
% 1.39/0.56  fof(f268,plain,(
% 1.39/0.56    spl4_27 <=> k1_xboole_0 = sK3),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.39/0.56  fof(f99,plain,(
% 1.39/0.56    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | spl4_6),
% 1.39/0.56    inference(avatar_component_clause,[],[f98])).
% 1.39/0.56  fof(f98,plain,(
% 1.39/0.56    spl4_6 <=> r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.39/0.56  fof(f271,plain,(
% 1.39/0.56    k1_xboole_0 != k1_relat_1(sK3) | sK3 != k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)) | sK3 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))),
% 1.39/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.39/0.56  fof(f270,plain,(
% 1.39/0.56    spl4_27 | ~spl4_25),
% 1.39/0.56    inference(avatar_split_clause,[],[f266,f251,f268])).
% 1.39/0.56  fof(f251,plain,(
% 1.39/0.56    spl4_25 <=> sK3 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.39/0.56  fof(f266,plain,(
% 1.39/0.56    k1_xboole_0 = sK3 | ~spl4_25),
% 1.39/0.56    inference(forward_demodulation,[],[f252,f66])).
% 1.39/0.56  fof(f66,plain,(
% 1.39/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.39/0.56    inference(equality_resolution,[],[f49])).
% 1.39/0.56  fof(f49,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f7])).
% 1.39/0.56  fof(f7,axiom,(
% 1.39/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.39/0.56  fof(f252,plain,(
% 1.39/0.56    sK3 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)) | ~spl4_25),
% 1.39/0.56    inference(avatar_component_clause,[],[f251])).
% 1.39/0.56  fof(f247,plain,(
% 1.39/0.56    ~spl4_4 | spl4_6 | ~spl4_24),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f246])).
% 1.39/0.56  fof(f246,plain,(
% 1.39/0.56    $false | (~spl4_4 | spl4_6 | ~spl4_24)),
% 1.39/0.56    inference(subsumption_resolution,[],[f241,f96])).
% 1.39/0.56  fof(f96,plain,(
% 1.39/0.56    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))) ) | ~spl4_4),
% 1.39/0.56    inference(resolution,[],[f89,f55])).
% 1.39/0.56  fof(f55,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f30])).
% 1.39/0.56  fof(f30,plain,(
% 1.39/0.56    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.39/0.56    inference(ennf_transformation,[],[f10])).
% 1.39/0.56  fof(f10,axiom,(
% 1.39/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.39/0.56  fof(f89,plain,(
% 1.39/0.56    v1_relat_1(sK3) | ~spl4_4),
% 1.39/0.56    inference(avatar_component_clause,[],[f88])).
% 1.39/0.56  fof(f88,plain,(
% 1.39/0.56    spl4_4 <=> v1_relat_1(sK3)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.39/0.56  fof(f241,plain,(
% 1.39/0.56    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | (spl4_6 | ~spl4_24)),
% 1.39/0.56    inference(superposition,[],[f99,f208])).
% 1.39/0.56  fof(f208,plain,(
% 1.39/0.56    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_24),
% 1.39/0.56    inference(avatar_component_clause,[],[f207])).
% 1.39/0.56  fof(f207,plain,(
% 1.39/0.56    spl4_24 <=> k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.39/0.56  fof(f225,plain,(
% 1.39/0.56    ~spl4_14 | spl4_20),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f224])).
% 1.39/0.56  fof(f224,plain,(
% 1.39/0.56    $false | (~spl4_14 | spl4_20)),
% 1.39/0.56    inference(subsumption_resolution,[],[f223,f45])).
% 1.39/0.56  fof(f45,plain,(
% 1.39/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f2])).
% 1.39/0.56  fof(f2,axiom,(
% 1.39/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.39/0.56  fof(f223,plain,(
% 1.39/0.56    ~r1_tarski(k1_xboole_0,sK3) | (~spl4_14 | spl4_20)),
% 1.39/0.56    inference(forward_demodulation,[],[f222,f66])).
% 1.39/0.56  fof(f222,plain,(
% 1.39/0.56    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)),sK3) | (~spl4_14 | spl4_20)),
% 1.39/0.56    inference(superposition,[],[f181,f150])).
% 1.39/0.56  fof(f150,plain,(
% 1.39/0.56    k1_xboole_0 = k1_relat_1(sK3) | ~spl4_14),
% 1.39/0.56    inference(avatar_component_clause,[],[f149])).
% 1.39/0.56  fof(f149,plain,(
% 1.39/0.56    spl4_14 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.39/0.56  fof(f181,plain,(
% 1.39/0.56    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3) | spl4_20),
% 1.39/0.56    inference(avatar_component_clause,[],[f180])).
% 1.39/0.56  fof(f180,plain,(
% 1.39/0.56    spl4_20 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.39/0.56  fof(f209,plain,(
% 1.39/0.56    spl4_24 | ~spl4_1 | ~spl4_3 | ~spl4_15),
% 1.39/0.56    inference(avatar_split_clause,[],[f205,f152,f78,f68,f207])).
% 1.39/0.56  fof(f68,plain,(
% 1.39/0.56    spl4_1 <=> v1_funct_1(sK3)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.39/0.56  fof(f78,plain,(
% 1.39/0.56    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.39/0.56  fof(f152,plain,(
% 1.39/0.56    spl4_15 <=> k1_tarski(sK0) = k1_relat_1(sK3)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.39/0.56  fof(f205,plain,(
% 1.39/0.56    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_15)),
% 1.39/0.56    inference(equality_resolution,[],[f162])).
% 1.39/0.56  fof(f162,plain,(
% 1.39/0.56    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) ) | (~spl4_1 | ~spl4_3 | ~spl4_15)),
% 1.39/0.56    inference(superposition,[],[f85,f153])).
% 1.39/0.56  fof(f153,plain,(
% 1.39/0.56    k1_tarski(sK0) = k1_relat_1(sK3) | ~spl4_15),
% 1.39/0.56    inference(avatar_component_clause,[],[f152])).
% 1.39/0.56  fof(f85,plain,(
% 1.39/0.56    ( ! [X0] : (k1_tarski(X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) ) | (~spl4_1 | ~spl4_3)),
% 1.39/0.56    inference(subsumption_resolution,[],[f72,f82])).
% 1.39/0.56  fof(f82,plain,(
% 1.39/0.56    v1_relat_1(sK3) | ~spl4_3),
% 1.39/0.56    inference(resolution,[],[f79,f52])).
% 1.39/0.56  fof(f52,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f27])).
% 1.39/0.56  fof(f27,plain,(
% 1.39/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.56    inference(ennf_transformation,[],[f13])).
% 1.39/0.56  fof(f13,axiom,(
% 1.39/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.39/0.56  fof(f79,plain,(
% 1.39/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~spl4_3),
% 1.39/0.56    inference(avatar_component_clause,[],[f78])).
% 1.39/0.56  fof(f72,plain,(
% 1.39/0.56    ( ! [X0] : (~v1_relat_1(sK3) | k1_tarski(X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) ) | ~spl4_1),
% 1.39/0.56    inference(resolution,[],[f69,f46])).
% 1.39/0.56  fof(f46,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f25])).
% 1.39/0.56  fof(f25,plain,(
% 1.39/0.56    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.39/0.56    inference(flattening,[],[f24])).
% 1.39/0.56  fof(f24,plain,(
% 1.39/0.56    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.39/0.56    inference(ennf_transformation,[],[f12])).
% 1.39/0.56  fof(f12,axiom,(
% 1.39/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.39/0.56  fof(f69,plain,(
% 1.39/0.56    v1_funct_1(sK3) | ~spl4_1),
% 1.39/0.56    inference(avatar_component_clause,[],[f68])).
% 1.39/0.56  fof(f182,plain,(
% 1.39/0.56    spl4_19 | ~spl4_20 | ~spl4_13),
% 1.39/0.56    inference(avatar_split_clause,[],[f145,f141,f180,f177])).
% 1.39/0.56  fof(f177,plain,(
% 1.39/0.56    spl4_19 <=> sK3 = k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.39/0.56  fof(f141,plain,(
% 1.39/0.56    spl4_13 <=> r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.39/0.56  fof(f145,plain,(
% 1.39/0.56    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)),sK3) | sK3 = k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)) | ~spl4_13),
% 1.39/0.56    inference(resolution,[],[f142,f44])).
% 1.39/0.56  fof(f44,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.39/0.56    inference(cnf_transformation,[],[f1])).
% 1.39/0.56  fof(f1,axiom,(
% 1.39/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.56  fof(f142,plain,(
% 1.39/0.56    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) | ~spl4_13),
% 1.39/0.56    inference(avatar_component_clause,[],[f141])).
% 1.39/0.56  fof(f154,plain,(
% 1.39/0.56    spl4_14 | spl4_15 | ~spl4_9),
% 1.39/0.56    inference(avatar_split_clause,[],[f118,f112,f152,f149])).
% 1.39/0.56  fof(f112,plain,(
% 1.39/0.56    spl4_9 <=> r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.39/0.56  fof(f118,plain,(
% 1.39/0.56    k1_tarski(sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3) | ~spl4_9),
% 1.39/0.56    inference(resolution,[],[f113,f39])).
% 1.39/0.56  fof(f39,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0) )),
% 1.39/0.56    inference(cnf_transformation,[],[f6])).
% 1.39/0.56  fof(f113,plain,(
% 1.39/0.56    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) | ~spl4_9),
% 1.39/0.56    inference(avatar_component_clause,[],[f112])).
% 1.39/0.56  fof(f143,plain,(
% 1.39/0.56    spl4_13 | ~spl4_10),
% 1.39/0.56    inference(avatar_split_clause,[],[f130,f122,f141])).
% 1.39/0.56  fof(f122,plain,(
% 1.39/0.56    spl4_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.39/0.56  fof(f130,plain,(
% 1.39/0.56    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) | ~spl4_10),
% 1.39/0.56    inference(resolution,[],[f123,f38])).
% 1.39/0.56  fof(f38,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f8])).
% 1.39/0.56  fof(f8,axiom,(
% 1.39/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.39/0.56  fof(f123,plain,(
% 1.39/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~spl4_10),
% 1.39/0.56    inference(avatar_component_clause,[],[f122])).
% 1.39/0.56  fof(f124,plain,(
% 1.39/0.56    spl4_10 | ~spl4_1 | ~spl4_3),
% 1.39/0.56    inference(avatar_split_clause,[],[f86,f78,f68,f122])).
% 1.39/0.56  fof(f86,plain,(
% 1.39/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | (~spl4_1 | ~spl4_3)),
% 1.39/0.56    inference(subsumption_resolution,[],[f71,f82])).
% 1.39/0.56  fof(f71,plain,(
% 1.39/0.56    ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~spl4_1),
% 1.39/0.56    inference(resolution,[],[f69,f53])).
% 1.39/0.56  fof(f53,plain,(
% 1.39/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f29])).
% 1.39/0.56  fof(f29,plain,(
% 1.39/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/0.56    inference(flattening,[],[f28])).
% 1.39/0.56  fof(f28,plain,(
% 1.39/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f20])).
% 1.39/0.56  fof(f20,plain,(
% 1.39/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)))),
% 1.39/0.56    inference(pure_predicate_removal,[],[f16])).
% 1.39/0.56  fof(f16,axiom,(
% 1.39/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.39/0.56  fof(f114,plain,(
% 1.39/0.56    spl4_9 | ~spl4_4 | ~spl4_7),
% 1.39/0.56    inference(avatar_split_clause,[],[f106,f102,f88,f112])).
% 1.39/0.56  fof(f102,plain,(
% 1.39/0.56    spl4_7 <=> v4_relat_1(sK3,k1_tarski(sK0))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.39/0.56  fof(f106,plain,(
% 1.39/0.56    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) | (~spl4_4 | ~spl4_7)),
% 1.39/0.56    inference(subsumption_resolution,[],[f105,f89])).
% 1.39/0.56  fof(f105,plain,(
% 1.39/0.56    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) | ~v1_relat_1(sK3) | ~spl4_7),
% 1.39/0.56    inference(resolution,[],[f103,f57])).
% 1.39/0.56  fof(f57,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f31])).
% 1.39/0.56  fof(f31,plain,(
% 1.39/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.39/0.56    inference(ennf_transformation,[],[f9])).
% 1.39/0.56  fof(f9,axiom,(
% 1.39/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.39/0.56  fof(f103,plain,(
% 1.39/0.56    v4_relat_1(sK3,k1_tarski(sK0)) | ~spl4_7),
% 1.39/0.56    inference(avatar_component_clause,[],[f102])).
% 1.39/0.56  fof(f104,plain,(
% 1.39/0.56    spl4_7 | ~spl4_3),
% 1.39/0.56    inference(avatar_split_clause,[],[f81,f78,f102])).
% 1.39/0.56  fof(f81,plain,(
% 1.39/0.56    v4_relat_1(sK3,k1_tarski(sK0)) | ~spl4_3),
% 1.39/0.56    inference(resolution,[],[f79,f59])).
% 1.39/0.56  fof(f59,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f32])).
% 1.39/0.56  fof(f32,plain,(
% 1.39/0.56    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.56    inference(ennf_transformation,[],[f21])).
% 1.39/0.56  fof(f21,plain,(
% 1.39/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.39/0.56    inference(pure_predicate_removal,[],[f14])).
% 1.39/0.56  fof(f14,axiom,(
% 1.39/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.39/0.56  fof(f100,plain,(
% 1.39/0.56    ~spl4_6 | ~spl4_3 | spl4_5),
% 1.39/0.56    inference(avatar_split_clause,[],[f95,f92,f78,f98])).
% 1.39/0.56  fof(f92,plain,(
% 1.39/0.56    spl4_5 <=> r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.39/0.56  fof(f95,plain,(
% 1.39/0.56    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | (~spl4_3 | spl4_5)),
% 1.39/0.56    inference(forward_demodulation,[],[f93,f83])).
% 1.39/0.56  fof(f83,plain,(
% 1.39/0.56    ( ! [X0] : (k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl4_3),
% 1.39/0.56    inference(resolution,[],[f79,f47])).
% 1.39/0.56  fof(f47,plain,(
% 1.39/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f26])).
% 1.39/0.56  fof(f26,plain,(
% 1.39/0.56    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.56    inference(ennf_transformation,[],[f15])).
% 1.39/0.56  fof(f15,axiom,(
% 1.39/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.39/0.56  fof(f93,plain,(
% 1.39/0.56    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | spl4_5),
% 1.39/0.56    inference(avatar_component_clause,[],[f92])).
% 1.39/0.56  fof(f94,plain,(
% 1.39/0.56    ~spl4_5),
% 1.39/0.56    inference(avatar_split_clause,[],[f36,f92])).
% 1.39/0.56  fof(f36,plain,(
% 1.39/0.56    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.39/0.56    inference(cnf_transformation,[],[f23])).
% 1.39/0.56  fof(f23,plain,(
% 1.39/0.56    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.39/0.56    inference(flattening,[],[f22])).
% 1.39/0.56  fof(f22,plain,(
% 1.39/0.56    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.39/0.56    inference(ennf_transformation,[],[f19])).
% 1.39/0.56  fof(f19,plain,(
% 1.39/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.39/0.56    inference(pure_predicate_removal,[],[f18])).
% 1.39/0.56  fof(f18,negated_conjecture,(
% 1.39/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.39/0.56    inference(negated_conjecture,[],[f17])).
% 1.39/0.56  fof(f17,conjecture,(
% 1.39/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.39/0.56  fof(f90,plain,(
% 1.39/0.56    spl4_4 | ~spl4_3),
% 1.39/0.56    inference(avatar_split_clause,[],[f82,f78,f88])).
% 1.39/0.56  fof(f80,plain,(
% 1.39/0.56    spl4_3),
% 1.39/0.56    inference(avatar_split_clause,[],[f34,f78])).
% 1.39/0.56  fof(f34,plain,(
% 1.39/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.39/0.56    inference(cnf_transformation,[],[f23])).
% 1.39/0.56  fof(f70,plain,(
% 1.39/0.56    spl4_1),
% 1.39/0.56    inference(avatar_split_clause,[],[f33,f68])).
% 1.39/0.56  fof(f33,plain,(
% 1.39/0.56    v1_funct_1(sK3)),
% 1.39/0.56    inference(cnf_transformation,[],[f23])).
% 1.39/0.56  % SZS output end Proof for theBenchmark
% 1.39/0.56  % (6954)------------------------------
% 1.39/0.56  % (6954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (6954)Termination reason: Refutation
% 1.39/0.56  
% 1.39/0.56  % (6954)Memory used [KB]: 6396
% 1.39/0.56  % (6954)Time elapsed: 0.147 s
% 1.39/0.56  % (6954)------------------------------
% 1.39/0.56  % (6954)------------------------------
% 1.39/0.56  % (6938)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.39/0.56  % (6953)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.39/0.57  % (6926)Success in time 0.183 s
%------------------------------------------------------------------------------
