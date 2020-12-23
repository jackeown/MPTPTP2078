%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 181 expanded)
%              Number of leaves         :   32 (  89 expanded)
%              Depth                    :    7
%              Number of atoms          :  274 ( 422 expanded)
%              Number of equality atoms :   76 ( 131 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f490,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f49,f53,f57,f61,f65,f69,f73,f77,f85,f92,f97,f102,f109,f124,f140,f214,f355,f390,f430,f448,f483])).

fof(f483,plain,
    ( ~ spl2_6
    | ~ spl2_22
    | spl2_59
    | ~ spl2_67 ),
    inference(avatar_contradiction_clause,[],[f482])).

fof(f482,plain,
    ( $false
    | ~ spl2_6
    | ~ spl2_22
    | spl2_59
    | ~ spl2_67 ),
    inference(subsumption_resolution,[],[f481,f389])).

fof(f389,plain,
    ( sK1 != k3_xboole_0(sK1,sK0)
    | spl2_59 ),
    inference(avatar_component_clause,[],[f387])).

fof(f387,plain,
    ( spl2_59
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f481,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_6
    | ~ spl2_22
    | ~ spl2_67 ),
    inference(forward_demodulation,[],[f455,f56])).

fof(f56,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl2_6
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f455,plain,
    ( k3_xboole_0(sK1,sK0) = k1_relat_1(k6_relat_1(sK1))
    | ~ spl2_22
    | ~ spl2_67 ),
    inference(superposition,[],[f139,f447])).

fof(f447,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK0)
    | ~ spl2_67 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl2_67
  <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f139,plain,
    ( ! [X6,X7] : k3_xboole_0(X6,X7) = k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl2_22
  <=> ! [X7,X6] : k3_xboole_0(X6,X7) = k1_relat_1(k7_relat_1(k6_relat_1(X6),X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f448,plain,
    ( spl2_67
    | ~ spl2_14
    | ~ spl2_64 ),
    inference(avatar_split_clause,[],[f443,f428,f89,f445])).

fof(f89,plain,
    ( spl2_14
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f428,plain,
    ( spl2_64
  <=> ! [X1,X0] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).

fof(f443,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK0)
    | ~ spl2_14
    | ~ spl2_64 ),
    inference(resolution,[],[f429,f91])).

fof(f91,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f89])).

fof(f429,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_64 ),
    inference(avatar_component_clause,[],[f428])).

fof(f430,plain,
    ( spl2_64
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f426,f106,f75,f63,f55,f47,f428])).

fof(f47,plain,
    ( spl2_4
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f63,plain,
    ( spl2_8
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f75,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k5_relat_1(k6_relat_1(X0),X1) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f106,plain,
    ( spl2_17
  <=> ! [X3,X2] : k6_relat_1(k3_xboole_0(X3,X2)) = k7_relat_1(k6_relat_1(X3),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f426,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f425,f107])).

fof(f107,plain,
    ( ! [X2,X3] : k6_relat_1(k3_xboole_0(X3,X2)) = k7_relat_1(k6_relat_1(X3),X2)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f106])).

fof(f425,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f424,f64])).

fof(f64,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f424,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) )
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f421,f48])).

fof(f48,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f421,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(superposition,[],[f76,f56])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X1),X0)
        | k5_relat_1(k6_relat_1(X0),X1) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f75])).

fof(f390,plain,
    ( ~ spl2_59
    | spl2_1
    | ~ spl2_52 ),
    inference(avatar_split_clause,[],[f376,f345,f33,f387])).

fof(f33,plain,
    ( spl2_1
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f345,plain,
    ( spl2_52
  <=> ! [X1,X0] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f376,plain,
    ( sK1 != k3_xboole_0(sK1,sK0)
    | spl2_1
    | ~ spl2_52 ),
    inference(superposition,[],[f35,f346])).

fof(f346,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f345])).

fof(f35,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f355,plain,
    ( spl2_52
    | ~ spl2_16
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f341,f212,f100,f345])).

fof(f100,plain,
    ( spl2_16
  <=> ! [X1,X0] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f212,plain,
    ( spl2_33
  <=> ! [X7,X6] : k3_xboole_0(X6,X7) = k2_relat_1(k7_relat_1(k6_relat_1(X7),X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f341,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_16
    | ~ spl2_33 ),
    inference(superposition,[],[f213,f101])).

fof(f101,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f100])).

fof(f213,plain,
    ( ! [X6,X7] : k3_xboole_0(X6,X7) = k2_relat_1(k7_relat_1(k6_relat_1(X7),X6))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f212])).

fof(f214,plain,
    ( spl2_33
    | ~ spl2_5
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f196,f121,f51,f212])).

fof(f51,plain,
    ( spl2_5
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f121,plain,
    ( spl2_18
  <=> ! [X1,X0] : k6_relat_1(k3_xboole_0(X1,X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f196,plain,
    ( ! [X6,X7] : k3_xboole_0(X6,X7) = k2_relat_1(k7_relat_1(k6_relat_1(X7),X6))
    | ~ spl2_5
    | ~ spl2_18 ),
    inference(superposition,[],[f52,f122])).

fof(f122,plain,
    ( ! [X0,X1] : k6_relat_1(k3_xboole_0(X1,X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f121])).

fof(f52,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f140,plain,
    ( spl2_22
    | ~ spl2_6
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f115,f106,f55,f138])).

fof(f115,plain,
    ( ! [X6,X7] : k3_xboole_0(X6,X7) = k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))
    | ~ spl2_6
    | ~ spl2_17 ),
    inference(superposition,[],[f56,f107])).

fof(f124,plain,
    ( spl2_18
    | ~ spl2_7
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f111,f106,f59,f121])).

fof(f59,plain,
    ( spl2_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f111,plain,
    ( ! [X2,X3] : k6_relat_1(k3_xboole_0(X3,X2)) = k7_relat_1(k6_relat_1(X2),X3)
    | ~ spl2_7
    | ~ spl2_17 ),
    inference(superposition,[],[f107,f60])).

fof(f60,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f109,plain,
    ( spl2_17
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f104,f95,f63,f106])).

fof(f95,plain,
    ( spl2_15
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f104,plain,
    ( ! [X0,X1] : k6_relat_1(k3_xboole_0(X1,X0)) = k7_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(superposition,[],[f64,f96])).

fof(f96,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f102,plain,
    ( spl2_16
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f98,f71,f47,f100])).

fof(f71,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f98,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(resolution,[],[f72,f48])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f97,plain,
    ( spl2_15
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f93,f67,f47,f95])).

fof(f67,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f93,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(resolution,[],[f68,f48])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f92,plain,
    ( spl2_14
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f86,f83,f38,f89])).

fof(f38,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f83,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f86,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(resolution,[],[f84,f40])).

fof(f40,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f83])).

fof(f85,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f30,f83])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f77,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f73,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f28,f71])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f69,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f65,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f26,f63])).

fof(f26,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f61,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f57,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f53,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f49,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f41,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f36,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f20,f33])).

fof(f20,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:19:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (9724)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (9723)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.44  % (9719)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.44  % (9728)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.44  % (9723)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f490,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f36,f41,f49,f53,f57,f61,f65,f69,f73,f77,f85,f92,f97,f102,f109,f124,f140,f214,f355,f390,f430,f448,f483])).
% 0.21/0.44  fof(f483,plain,(
% 0.21/0.44    ~spl2_6 | ~spl2_22 | spl2_59 | ~spl2_67),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f482])).
% 0.21/0.44  fof(f482,plain,(
% 0.21/0.44    $false | (~spl2_6 | ~spl2_22 | spl2_59 | ~spl2_67)),
% 0.21/0.44    inference(subsumption_resolution,[],[f481,f389])).
% 0.21/0.44  fof(f389,plain,(
% 0.21/0.44    sK1 != k3_xboole_0(sK1,sK0) | spl2_59),
% 0.21/0.44    inference(avatar_component_clause,[],[f387])).
% 0.21/0.44  fof(f387,plain,(
% 0.21/0.44    spl2_59 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 0.21/0.44  fof(f481,plain,(
% 0.21/0.44    sK1 = k3_xboole_0(sK1,sK0) | (~spl2_6 | ~spl2_22 | ~spl2_67)),
% 0.21/0.44    inference(forward_demodulation,[],[f455,f56])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f55])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    spl2_6 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.44  fof(f455,plain,(
% 0.21/0.44    k3_xboole_0(sK1,sK0) = k1_relat_1(k6_relat_1(sK1)) | (~spl2_22 | ~spl2_67)),
% 0.21/0.44    inference(superposition,[],[f139,f447])).
% 0.21/0.44  fof(f447,plain,(
% 0.21/0.44    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK0) | ~spl2_67),
% 0.21/0.44    inference(avatar_component_clause,[],[f445])).
% 0.21/0.44  fof(f445,plain,(
% 0.21/0.44    spl2_67 <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 0.21/0.44  fof(f139,plain,(
% 0.21/0.44    ( ! [X6,X7] : (k3_xboole_0(X6,X7) = k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))) ) | ~spl2_22),
% 0.21/0.44    inference(avatar_component_clause,[],[f138])).
% 0.21/0.44  fof(f138,plain,(
% 0.21/0.44    spl2_22 <=> ! [X7,X6] : k3_xboole_0(X6,X7) = k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.44  fof(f448,plain,(
% 0.21/0.44    spl2_67 | ~spl2_14 | ~spl2_64),
% 0.21/0.44    inference(avatar_split_clause,[],[f443,f428,f89,f445])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    spl2_14 <=> r1_tarski(sK1,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.44  fof(f428,plain,(
% 0.21/0.44    spl2_64 <=> ! [X1,X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~r1_tarski(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).
% 0.21/0.44  fof(f443,plain,(
% 0.21/0.44    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK0) | (~spl2_14 | ~spl2_64)),
% 0.21/0.44    inference(resolution,[],[f429,f91])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    r1_tarski(sK1,sK0) | ~spl2_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f89])).
% 0.21/0.44  fof(f429,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_64),
% 0.21/0.44    inference(avatar_component_clause,[],[f428])).
% 0.21/0.44  fof(f430,plain,(
% 0.21/0.44    spl2_64 | ~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_11 | ~spl2_17),
% 0.21/0.44    inference(avatar_split_clause,[],[f426,f106,f75,f63,f55,f47,f428])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    spl2_4 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    spl2_8 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    spl2_11 <=> ! [X1,X0] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    spl2_17 <=> ! [X3,X2] : k6_relat_1(k3_xboole_0(X3,X2)) = k7_relat_1(k6_relat_1(X3),X2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.44  fof(f426,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~r1_tarski(X0,X1)) ) | (~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_11 | ~spl2_17)),
% 0.21/0.44    inference(forward_demodulation,[],[f425,f107])).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    ( ! [X2,X3] : (k6_relat_1(k3_xboole_0(X3,X2)) = k7_relat_1(k6_relat_1(X3),X2)) ) | ~spl2_17),
% 0.21/0.44    inference(avatar_component_clause,[],[f106])).
% 0.21/0.44  fof(f425,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) ) | (~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_11)),
% 0.21/0.44    inference(forward_demodulation,[],[f424,f64])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) ) | ~spl2_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f63])).
% 0.21/0.44  fof(f424,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ) | (~spl2_4 | ~spl2_6 | ~spl2_11)),
% 0.21/0.44    inference(subsumption_resolution,[],[f421,f48])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f47])).
% 0.21/0.44  fof(f421,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_6 | ~spl2_11)),
% 0.21/0.44    inference(superposition,[],[f76,f56])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) ) | ~spl2_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f75])).
% 0.21/0.44  fof(f390,plain,(
% 0.21/0.44    ~spl2_59 | spl2_1 | ~spl2_52),
% 0.21/0.44    inference(avatar_split_clause,[],[f376,f345,f33,f387])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    spl2_1 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f345,plain,(
% 0.21/0.44    spl2_52 <=> ! [X1,X0] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 0.21/0.44  fof(f376,plain,(
% 0.21/0.44    sK1 != k3_xboole_0(sK1,sK0) | (spl2_1 | ~spl2_52)),
% 0.21/0.44    inference(superposition,[],[f35,f346])).
% 0.21/0.44  fof(f346,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_52),
% 0.21/0.44    inference(avatar_component_clause,[],[f345])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) | spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f33])).
% 0.21/0.44  fof(f355,plain,(
% 0.21/0.44    spl2_52 | ~spl2_16 | ~spl2_33),
% 0.21/0.44    inference(avatar_split_clause,[],[f341,f212,f100,f345])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    spl2_16 <=> ! [X1,X0] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.44  fof(f212,plain,(
% 0.21/0.44    spl2_33 <=> ! [X7,X6] : k3_xboole_0(X6,X7) = k2_relat_1(k7_relat_1(k6_relat_1(X7),X6))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.21/0.44  fof(f341,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_16 | ~spl2_33)),
% 0.21/0.44    inference(superposition,[],[f213,f101])).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | ~spl2_16),
% 0.21/0.44    inference(avatar_component_clause,[],[f100])).
% 0.21/0.44  fof(f213,plain,(
% 0.21/0.44    ( ! [X6,X7] : (k3_xboole_0(X6,X7) = k2_relat_1(k7_relat_1(k6_relat_1(X7),X6))) ) | ~spl2_33),
% 0.21/0.44    inference(avatar_component_clause,[],[f212])).
% 0.21/0.44  fof(f214,plain,(
% 0.21/0.44    spl2_33 | ~spl2_5 | ~spl2_18),
% 0.21/0.44    inference(avatar_split_clause,[],[f196,f121,f51,f212])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    spl2_5 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.44  fof(f121,plain,(
% 0.21/0.44    spl2_18 <=> ! [X1,X0] : k6_relat_1(k3_xboole_0(X1,X0)) = k7_relat_1(k6_relat_1(X0),X1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.44  fof(f196,plain,(
% 0.21/0.44    ( ! [X6,X7] : (k3_xboole_0(X6,X7) = k2_relat_1(k7_relat_1(k6_relat_1(X7),X6))) ) | (~spl2_5 | ~spl2_18)),
% 0.21/0.44    inference(superposition,[],[f52,f122])).
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X1,X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_18),
% 0.21/0.44    inference(avatar_component_clause,[],[f121])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f51])).
% 0.21/0.44  fof(f140,plain,(
% 0.21/0.44    spl2_22 | ~spl2_6 | ~spl2_17),
% 0.21/0.44    inference(avatar_split_clause,[],[f115,f106,f55,f138])).
% 0.21/0.44  fof(f115,plain,(
% 0.21/0.44    ( ! [X6,X7] : (k3_xboole_0(X6,X7) = k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))) ) | (~spl2_6 | ~spl2_17)),
% 0.21/0.44    inference(superposition,[],[f56,f107])).
% 0.21/0.44  fof(f124,plain,(
% 0.21/0.44    spl2_18 | ~spl2_7 | ~spl2_17),
% 0.21/0.44    inference(avatar_split_clause,[],[f111,f106,f59,f121])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    spl2_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.44  fof(f111,plain,(
% 0.21/0.44    ( ! [X2,X3] : (k6_relat_1(k3_xboole_0(X3,X2)) = k7_relat_1(k6_relat_1(X2),X3)) ) | (~spl2_7 | ~spl2_17)),
% 0.21/0.44    inference(superposition,[],[f107,f60])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f59])).
% 0.21/0.44  fof(f109,plain,(
% 0.21/0.44    spl2_17 | ~spl2_8 | ~spl2_15),
% 0.21/0.44    inference(avatar_split_clause,[],[f104,f95,f63,f106])).
% 0.21/0.44  fof(f95,plain,(
% 0.21/0.44    spl2_15 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.44  fof(f104,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X1,X0)) = k7_relat_1(k6_relat_1(X1),X0)) ) | (~spl2_8 | ~spl2_15)),
% 0.21/0.44    inference(superposition,[],[f64,f96])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f95])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    spl2_16 | ~spl2_4 | ~spl2_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f98,f71,f47,f100])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    spl2_10 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.44  fof(f98,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_4 | ~spl2_10)),
% 0.21/0.44    inference(resolution,[],[f72,f48])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f71])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    spl2_15 | ~spl2_4 | ~spl2_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f93,f67,f47,f95])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    spl2_9 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_4 | ~spl2_9)),
% 0.21/0.44    inference(resolution,[],[f68,f48])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f67])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    spl2_14 | ~spl2_2 | ~spl2_13),
% 0.21/0.44    inference(avatar_split_clause,[],[f86,f83,f38,f89])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    spl2_13 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    r1_tarski(sK1,sK0) | (~spl2_2 | ~spl2_13)),
% 0.21/0.44    inference(resolution,[],[f84,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f38])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_13),
% 0.21/0.45    inference(avatar_component_clause,[],[f83])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    spl2_13),
% 0.21/0.45    inference(avatar_split_clause,[],[f30,f83])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.45    inference(nnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    spl2_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f29,f75])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(flattening,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    spl2_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f28,f71])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    spl2_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f27,f67])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    spl2_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f26,f63])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    spl2_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f25,f59])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    spl2_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f23,f55])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    spl2_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f24,f51])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    spl2_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f21,f47])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    spl2_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f19,f38])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.21/0.45    inference(negated_conjecture,[],[f9])).
% 0.21/0.45  fof(f9,conjecture,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ~spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f20,f33])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (9723)------------------------------
% 0.21/0.45  % (9723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (9723)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (9723)Memory used [KB]: 10874
% 0.21/0.45  % (9723)Time elapsed: 0.021 s
% 0.21/0.45  % (9723)------------------------------
% 0.21/0.45  % (9723)------------------------------
% 0.21/0.45  % (9717)Success in time 0.084 s
%------------------------------------------------------------------------------
