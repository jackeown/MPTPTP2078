%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 224 expanded)
%              Number of leaves         :   34 (  97 expanded)
%              Depth                    :    8
%              Number of atoms          :  283 ( 595 expanded)
%              Number of equality atoms :   52 (  85 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1949,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f88,f93,f98,f206,f211,f262,f263,f264,f265,f318,f319,f448,f548,f560,f576,f616,f992,f1848,f1906,f1948])).

fof(f1948,plain,
    ( k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1)
    | sK1 != k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | k3_subset_1(sK0,k3_subset_1(sK0,sK1)) != k4_xboole_0(sK0,k3_subset_1(sK0,sK1))
    | k3_subset_1(sK0,sK2) != k4_xboole_0(sK0,sK2)
    | sK2 != k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | k3_subset_1(sK0,k3_subset_1(sK0,sK2)) != k4_xboole_0(sK0,k3_subset_1(sK0,sK2))
    | r1_tarski(sK1,sK2)
    | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1906,plain,
    ( spl3_59
    | ~ spl3_28
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f1901,f1845,f545,f1903])).

fof(f1903,plain,
    ( spl3_59
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f545,plain,
    ( spl3_28
  <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f1845,plain,
    ( spl3_57
  <=> r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f1901,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl3_28
    | ~ spl3_57 ),
    inference(forward_demodulation,[],[f1900,f101])).

fof(f101,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f52,f49])).

fof(f49,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1900,plain,
    ( r1_tarski(k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl3_28
    | ~ spl3_57 ),
    inference(forward_demodulation,[],[f1875,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1875,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl3_28
    | ~ spl3_57 ),
    inference(unit_resulting_resolution,[],[f546,f1847,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).

fof(f1847,plain,
    ( r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK0)
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f1845])).

fof(f546,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f545])).

fof(f1848,plain,
    ( spl3_57
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f1809,f988,f1845])).

fof(f988,plain,
    ( spl3_37
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f1809,plain,
    ( r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK0)
    | ~ spl3_37 ),
    inference(superposition,[],[f192,f990])).

fof(f990,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f988])).

fof(f192,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[],[f75,f50])).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f75,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) ),
    inference(definition_unfolding,[],[f65,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f65,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f992,plain,
    ( spl3_37
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f975,f564,f988])).

fof(f564,plain,
    ( spl3_30
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f975,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_30 ),
    inference(superposition,[],[f67,f566])).

fof(f566,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f564])).

fof(f616,plain,
    ( spl3_30
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f593,f545,f564])).

fof(f593,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_28 ),
    inference(resolution,[],[f546,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f576,plain,
    ( spl3_28
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f575,f258,f253,f84,f545])).

fof(f84,plain,
    ( spl3_2
  <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f253,plain,
    ( spl3_15
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f258,plain,
    ( spl3_16
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f575,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f574,f260])).

fof(f260,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f258])).

fof(f574,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f85,f255])).

fof(f255,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f253])).

fof(f85,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f560,plain,
    ( ~ spl3_1
    | spl3_28 ),
    inference(avatar_contradiction_clause,[],[f557])).

fof(f557,plain,
    ( $false
    | ~ spl3_1
    | spl3_28 ),
    inference(unit_resulting_resolution,[],[f112,f81,f547,f71])).

fof(f547,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl3_28 ),
    inference(avatar_component_clause,[],[f545])).

fof(f81,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f112,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(unit_resulting_resolution,[],[f99,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f51,f49])).

fof(f51,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f548,plain,
    ( ~ spl3_28
    | ~ spl3_16
    | spl3_22 ),
    inference(avatar_split_clause,[],[f541,f445,f258,f545])).

fof(f445,plain,
    ( spl3_22
  <=> r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f541,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_16
    | spl3_22 ),
    inference(backward_demodulation,[],[f447,f260])).

fof(f447,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f445])).

fof(f448,plain,
    ( ~ spl3_22
    | spl3_2
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f441,f253,f84,f445])).

fof(f441,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl3_2
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f86,f255])).

fof(f86,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f319,plain,
    ( spl3_19
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f294,f95,f309])).

fof(f309,plain,
    ( spl3_19
  <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f95,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f294,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_4 ),
    inference(resolution,[],[f60,f97])).

fof(f97,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f318,plain,
    ( spl3_20
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f293,f90,f314])).

fof(f314,plain,
    ( spl3_20
  <=> sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f90,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f293,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_3 ),
    inference(resolution,[],[f60,f92])).

fof(f92,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f265,plain,
    ( spl3_13
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f240,f208,f243])).

fof(f243,plain,
    ( spl3_13
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f208,plain,
    ( spl3_10
  <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f240,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_10 ),
    inference(resolution,[],[f59,f210])).

fof(f210,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f208])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f264,plain,
    ( spl3_14
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f239,f203,f248])).

fof(f248,plain,
    ( spl3_14
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f203,plain,
    ( spl3_9
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f239,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_9 ),
    inference(resolution,[],[f59,f205])).

fof(f205,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f203])).

fof(f263,plain,
    ( spl3_15
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f238,f95,f253])).

fof(f238,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f59,f97])).

fof(f262,plain,
    ( spl3_16
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f237,f90,f258])).

fof(f237,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f59,f92])).

fof(f211,plain,
    ( spl3_10
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f200,f90,f208])).

fof(f200,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f92,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f206,plain,
    ( spl3_9
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f201,f95,f203])).

fof(f201,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f97,f58])).

fof(f98,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f42,f95])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | ~ r1_tarski(sK1,X2) )
        & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | r1_tarski(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | ~ r1_tarski(sK1,sK2) )
      & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | r1_tarski(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f93,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f43,f90])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f88,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f44,f84,f80])).

fof(f44,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f87,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f45,f84,f80])).

fof(f45,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (2124)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (2118)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (2120)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (2122)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (2127)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (2119)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (2115)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (2126)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (2113)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (2125)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (2117)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (2116)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (2130)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (2114)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.51  % (2121)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.51  % (2128)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.52  % (2129)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.52  % (2123)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.52  % (2119)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f1949,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f87,f88,f93,f98,f206,f211,f262,f263,f264,f265,f318,f319,f448,f548,f560,f576,f616,f992,f1848,f1906,f1948])).
% 0.20/0.52  fof(f1948,plain,(
% 0.20/0.52    k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1) | sK1 != k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | k3_subset_1(sK0,k3_subset_1(sK0,sK1)) != k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) | k3_subset_1(sK0,sK2) != k4_xboole_0(sK0,sK2) | sK2 != k3_subset_1(sK0,k3_subset_1(sK0,sK2)) | k3_subset_1(sK0,k3_subset_1(sK0,sK2)) != k4_xboole_0(sK0,k3_subset_1(sK0,sK2)) | r1_tarski(sK1,sK2) | ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f1906,plain,(
% 0.20/0.53    spl3_59 | ~spl3_28 | ~spl3_57),
% 0.20/0.53    inference(avatar_split_clause,[],[f1901,f1845,f545,f1903])).
% 0.20/0.53  fof(f1903,plain,(
% 0.20/0.53    spl3_59 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.20/0.53  fof(f545,plain,(
% 0.20/0.53    spl3_28 <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.53  fof(f1845,plain,(
% 0.20/0.53    spl3_57 <=> r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.20/0.53  fof(f1901,plain,(
% 0.20/0.53    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | (~spl3_28 | ~spl3_57)),
% 0.20/0.53    inference(forward_demodulation,[],[f1900,f101])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.53    inference(superposition,[],[f52,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.53  fof(f1900,plain,(
% 0.20/0.53    r1_tarski(k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | (~spl3_28 | ~spl3_57)),
% 0.20/0.53    inference(forward_demodulation,[],[f1875,f67])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.53  fof(f1875,plain,(
% 0.20/0.53    r1_tarski(k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | (~spl3_28 | ~spl3_57)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f546,f1847,f71])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).
% 0.20/0.53  fof(f1847,plain,(
% 0.20/0.53    r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK0) | ~spl3_57),
% 0.20/0.53    inference(avatar_component_clause,[],[f1845])).
% 0.20/0.53  fof(f546,plain,(
% 0.20/0.53    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl3_28),
% 0.20/0.53    inference(avatar_component_clause,[],[f545])).
% 0.20/0.53  fof(f1848,plain,(
% 0.20/0.53    spl3_57 | ~spl3_37),
% 0.20/0.53    inference(avatar_split_clause,[],[f1809,f988,f1845])).
% 0.20/0.53  fof(f988,plain,(
% 0.20/0.53    spl3_37 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.20/0.53  fof(f1809,plain,(
% 0.20/0.53    r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK0) | ~spl3_37),
% 0.20/0.53    inference(superposition,[],[f192,f990])).
% 0.20/0.53  fof(f990,plain,(
% 0.20/0.53    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | ~spl3_37),
% 0.20/0.53    inference(avatar_component_clause,[],[f988])).
% 0.20/0.53  fof(f192,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 0.20/0.53    inference(superposition,[],[f75,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.53    inference(rectify,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f65,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).
% 0.20/0.53  fof(f992,plain,(
% 0.20/0.53    spl3_37 | ~spl3_30),
% 0.20/0.53    inference(avatar_split_clause,[],[f975,f564,f988])).
% 0.20/0.53  fof(f564,plain,(
% 0.20/0.53    spl3_30 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.53  fof(f975,plain,(
% 0.20/0.53    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | ~spl3_30),
% 0.20/0.53    inference(superposition,[],[f67,f566])).
% 0.20/0.53  fof(f566,plain,(
% 0.20/0.53    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl3_30),
% 0.20/0.53    inference(avatar_component_clause,[],[f564])).
% 0.20/0.53  fof(f616,plain,(
% 0.20/0.53    spl3_30 | ~spl3_28),
% 0.20/0.53    inference(avatar_split_clause,[],[f593,f545,f564])).
% 0.20/0.53  fof(f593,plain,(
% 0.20/0.53    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl3_28),
% 0.20/0.53    inference(resolution,[],[f546,f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.53    inference(nnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.53  fof(f576,plain,(
% 0.20/0.53    spl3_28 | ~spl3_2 | ~spl3_15 | ~spl3_16),
% 0.20/0.53    inference(avatar_split_clause,[],[f575,f258,f253,f84,f545])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    spl3_2 <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.53  fof(f253,plain,(
% 0.20/0.53    spl3_15 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.53  fof(f258,plain,(
% 0.20/0.53    spl3_16 <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.53  fof(f575,plain,(
% 0.20/0.53    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | (~spl3_2 | ~spl3_15 | ~spl3_16)),
% 0.20/0.53    inference(forward_demodulation,[],[f574,f260])).
% 0.20/0.53  fof(f260,plain,(
% 0.20/0.53    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl3_16),
% 0.20/0.53    inference(avatar_component_clause,[],[f258])).
% 0.20/0.53  fof(f574,plain,(
% 0.20/0.53    r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | (~spl3_2 | ~spl3_15)),
% 0.20/0.53    inference(forward_demodulation,[],[f85,f255])).
% 0.20/0.53  fof(f255,plain,(
% 0.20/0.53    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_15),
% 0.20/0.53    inference(avatar_component_clause,[],[f253])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~spl3_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f84])).
% 0.20/0.53  fof(f560,plain,(
% 0.20/0.53    ~spl3_1 | spl3_28),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f557])).
% 0.20/0.53  fof(f557,plain,(
% 0.20/0.53    $false | (~spl3_1 | spl3_28)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f112,f81,f547,f71])).
% 0.20/0.53  fof(f547,plain,(
% 0.20/0.53    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | spl3_28),
% 0.20/0.53    inference(avatar_component_clause,[],[f545])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    r1_tarski(sK1,sK2) | ~spl3_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f80])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    spl3_1 <=> r1_tarski(sK1,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f99,f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.53    inference(superposition,[],[f51,f49])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.53  fof(f548,plain,(
% 0.20/0.53    ~spl3_28 | ~spl3_16 | spl3_22),
% 0.20/0.53    inference(avatar_split_clause,[],[f541,f445,f258,f545])).
% 0.20/0.53  fof(f445,plain,(
% 0.20/0.53    spl3_22 <=> r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.53  fof(f541,plain,(
% 0.20/0.53    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | (~spl3_16 | spl3_22)),
% 0.20/0.53    inference(backward_demodulation,[],[f447,f260])).
% 0.20/0.53  fof(f447,plain,(
% 0.20/0.53    ~r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | spl3_22),
% 0.20/0.53    inference(avatar_component_clause,[],[f445])).
% 0.20/0.53  fof(f448,plain,(
% 0.20/0.53    ~spl3_22 | spl3_2 | ~spl3_15),
% 0.20/0.53    inference(avatar_split_clause,[],[f441,f253,f84,f445])).
% 0.20/0.53  fof(f441,plain,(
% 0.20/0.53    ~r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | (spl3_2 | ~spl3_15)),
% 0.20/0.53    inference(backward_demodulation,[],[f86,f255])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | spl3_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f84])).
% 0.20/0.53  fof(f319,plain,(
% 0.20/0.53    spl3_19 | ~spl3_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f294,f95,f309])).
% 0.20/0.53  fof(f309,plain,(
% 0.20/0.53    spl3_19 <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.53  fof(f294,plain,(
% 0.20/0.53    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl3_4),
% 0.20/0.53    inference(resolution,[],[f60,f97])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f95])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.53  fof(f318,plain,(
% 0.20/0.53    spl3_20 | ~spl3_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f293,f90,f314])).
% 0.20/0.53  fof(f314,plain,(
% 0.20/0.53    spl3_20 <=> sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.53  fof(f293,plain,(
% 0.20/0.53    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) | ~spl3_3),
% 0.20/0.53    inference(resolution,[],[f60,f92])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f90])).
% 0.20/0.53  fof(f265,plain,(
% 0.20/0.53    spl3_13 | ~spl3_10),
% 0.20/0.53    inference(avatar_split_clause,[],[f240,f208,f243])).
% 0.20/0.53  fof(f243,plain,(
% 0.20/0.53    spl3_13 <=> k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.53  fof(f208,plain,(
% 0.20/0.53    spl3_10 <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.53  fof(f240,plain,(
% 0.20/0.53    k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK2)) | ~spl3_10),
% 0.20/0.53    inference(resolution,[],[f59,f210])).
% 0.20/0.53  fof(f210,plain,(
% 0.20/0.53    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f208])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.53  fof(f264,plain,(
% 0.20/0.53    spl3_14 | ~spl3_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f239,f203,f248])).
% 0.20/0.53  fof(f248,plain,(
% 0.20/0.53    spl3_14 <=> k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.53  fof(f203,plain,(
% 0.20/0.53    spl3_9 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.53  fof(f239,plain,(
% 0.20/0.53    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) | ~spl3_9),
% 0.20/0.53    inference(resolution,[],[f59,f205])).
% 0.20/0.53  fof(f205,plain,(
% 0.20/0.53    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f203])).
% 0.20/0.53  fof(f263,plain,(
% 0.20/0.53    spl3_15 | ~spl3_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f238,f95,f253])).
% 0.20/0.53  fof(f238,plain,(
% 0.20/0.53    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_4),
% 0.20/0.53    inference(resolution,[],[f59,f97])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    spl3_16 | ~spl3_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f237,f90,f258])).
% 0.20/0.53  fof(f237,plain,(
% 0.20/0.53    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl3_3),
% 0.20/0.53    inference(resolution,[],[f59,f92])).
% 0.20/0.53  fof(f211,plain,(
% 0.20/0.53    spl3_10 | ~spl3_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f200,f90,f208])).
% 0.20/0.53  fof(f200,plain,(
% 0.20/0.53    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f92,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.53  fof(f206,plain,(
% 0.20/0.53    spl3_9 | ~spl3_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f201,f95,f203])).
% 0.20/0.53  fof(f201,plain,(
% 0.20/0.53    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f97,f58])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    spl3_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f42,f95])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f38,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(flattening,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(nnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.20/0.53    inference(negated_conjecture,[],[f25])).
% 0.20/0.53  fof(f25,conjecture,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    spl3_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f43,f90])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    spl3_1 | spl3_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f44,f84,f80])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ~spl3_1 | ~spl3_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f45,f84,f80])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (2119)------------------------------
% 0.20/0.53  % (2119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2119)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (2119)Memory used [KB]: 7291
% 0.20/0.53  % (2119)Time elapsed: 0.051 s
% 0.20/0.53  % (2119)------------------------------
% 0.20/0.53  % (2119)------------------------------
% 0.20/0.53  % (2112)Success in time 0.173 s
%------------------------------------------------------------------------------
