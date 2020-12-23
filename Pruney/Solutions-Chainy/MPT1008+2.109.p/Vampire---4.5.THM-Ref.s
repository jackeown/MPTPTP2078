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
% DateTime   : Thu Dec  3 13:04:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 240 expanded)
%              Number of leaves         :   34 (  99 expanded)
%              Depth                    :    9
%              Number of atoms          :  314 ( 540 expanded)
%              Number of equality atoms :   96 ( 204 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f251,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f102,f107,f111,f121,f138,f152,f163,f175,f195,f204,f210,f222,f227,f246,f250])).

fof(f250,plain,(
    spl3_22 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | spl3_22 ),
    inference(unit_resulting_resolution,[],[f36,f245])).

fof(f245,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl3_22
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f246,plain,
    ( ~ spl3_22
    | ~ spl3_13
    | spl3_15 ),
    inference(avatar_split_clause,[],[f235,f160,f140,f243])).

fof(f140,plain,
    ( spl3_13
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f160,plain,
    ( spl3_15
  <=> v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f235,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_13
    | spl3_15 ),
    inference(backward_demodulation,[],[f162,f141])).

fof(f141,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f140])).

fof(f162,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f160])).

fof(f227,plain,
    ( ~ spl3_17
    | spl3_21 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | ~ spl3_17
    | spl3_21 ),
    inference(unit_resulting_resolution,[],[f174,f221,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f221,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | spl3_21 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl3_21
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f174,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl3_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f222,plain,
    ( ~ spl3_21
    | spl3_9
    | ~ spl3_14
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f217,f192,f149,f118,f219])).

fof(f118,plain,
    ( spl3_9
  <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k11_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f149,plain,
    ( spl3_14
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f192,plain,
    ( spl3_19
  <=> k2_relat_1(sK2) = k11_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f217,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | spl3_9
    | ~ spl3_14
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f208,f194])).

fof(f194,plain,
    ( k2_relat_1(sK2) = k11_relat_1(sK2,sK0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f192])).

fof(f208,plain,
    ( k11_relat_1(sK2,sK0) != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | spl3_9
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f120,f151])).

fof(f151,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f149])).

fof(f120,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k11_relat_1(sK2,sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f210,plain,
    ( ~ spl3_5
    | ~ spl3_10
    | spl3_13 ),
    inference(avatar_split_clause,[],[f145,f140,f124,f95])).

fof(f95,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f124,plain,
    ( spl3_10
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f145,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_13 ),
    inference(trivial_inequality_removal,[],[f144])).

fof(f144,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_13 ),
    inference(superposition,[],[f142,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f142,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f140])).

fof(f204,plain,
    ( spl3_8
    | ~ spl3_5
    | spl3_10
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f201,f192,f124,f95,f114])).

fof(f114,plain,
    ( spl3_8
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f201,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl3_19 ),
    inference(superposition,[],[f194,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f195,plain,
    ( ~ spl3_5
    | spl3_19
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f189,f149,f192,f95])).

fof(f189,plain,
    ( k2_relat_1(sK2) = k11_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_14 ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( k2_relat_1(sK2) = k11_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_14 ),
    inference(superposition,[],[f39,f157])).

fof(f157,plain,
    ( ! [X0] :
        ( k11_relat_1(X0,sK0) = k9_relat_1(X0,k1_relat_1(sK2))
        | ~ v1_relat_1(X0) )
    | ~ spl3_14 ),
    inference(superposition,[],[f64,f151])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f39,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f175,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f155,f149,f87,f172])).

fof(f87,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f155,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f89,f151])).

fof(f89,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f163,plain,
    ( ~ spl3_15
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f158,f149,f160])).

fof(f158,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl3_14 ),
    inference(superposition,[],[f63,f151])).

fof(f63,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f37,f59])).

fof(f37,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f152,plain,
    ( ~ spl3_4
    | spl3_14
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f146,f135,f149,f87])).

fof(f135,plain,
    ( spl3_12
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f146,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl3_12 ),
    inference(superposition,[],[f137,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f137,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f135])).

fof(f138,plain,
    ( ~ spl3_3
    | spl3_12
    | spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f92,f87,f77,f135,f82])).

fof(f82,plain,
    ( spl3_3
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f77,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f92,plain,
    ( k1_xboole_0 = sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f89,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f121,plain,
    ( ~ spl3_5
    | ~ spl3_8
    | ~ spl3_1
    | ~ spl3_9
    | spl3_7 ),
    inference(avatar_split_clause,[],[f112,f104,f118,f72,f114,f95])).

fof(f72,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f104,plain,
    ( spl3_7
  <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f112,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k11_relat_1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(superposition,[],[f106,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f106,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f111,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f44,f101])).

fof(f101,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_6
  <=> v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f107,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f60,f104])).

fof(f60,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f35,f59,f59])).

fof(f35,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f102,plain,
    ( spl3_5
    | ~ spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f93,f87,f99,f95])).

fof(f93,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f89,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f90,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f61,f87])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f33,f59])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f85,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f62,f82])).

fof(f62,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f32,f59])).

fof(f32,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f80,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f34,f77])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:36:45 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.52  % (15638)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (15630)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (15630)Refutation not found, incomplete strategy% (15630)------------------------------
% 0.22/0.52  % (15630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15620)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (15630)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15630)Memory used [KB]: 6140
% 0.22/0.52  % (15630)Time elapsed: 0.004 s
% 0.22/0.52  % (15630)------------------------------
% 0.22/0.52  % (15630)------------------------------
% 0.22/0.53  % (15619)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (15626)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (15638)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (15624)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f251,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f102,f107,f111,f121,f138,f152,f163,f175,f195,f204,f210,f222,f227,f246,f250])).
% 0.22/0.53  fof(f250,plain,(
% 0.22/0.53    spl3_22),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f247])).
% 0.22/0.53  fof(f247,plain,(
% 0.22/0.53    $false | spl3_22),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f36,f245])).
% 0.22/0.53  fof(f245,plain,(
% 0.22/0.53    ~v1_xboole_0(k1_xboole_0) | spl3_22),
% 0.22/0.53    inference(avatar_component_clause,[],[f243])).
% 0.22/0.53  fof(f243,plain,(
% 0.22/0.53    spl3_22 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.53  fof(f246,plain,(
% 0.22/0.53    ~spl3_22 | ~spl3_13 | spl3_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f235,f160,f140,f243])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    spl3_13 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    spl3_15 <=> v1_xboole_0(k1_relat_1(sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    ~v1_xboole_0(k1_xboole_0) | (~spl3_13 | spl3_15)),
% 0.22/0.53    inference(backward_demodulation,[],[f162,f141])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(sK2) | ~spl3_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f140])).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    ~v1_xboole_0(k1_relat_1(sK2)) | spl3_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f160])).
% 0.22/0.53  fof(f227,plain,(
% 0.22/0.53    ~spl3_17 | spl3_21),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f223])).
% 0.22/0.53  fof(f223,plain,(
% 0.22/0.53    $false | (~spl3_17 | spl3_21)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f174,f221,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.53  fof(f221,plain,(
% 0.22/0.53    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | spl3_21),
% 0.22/0.53    inference(avatar_component_clause,[],[f219])).
% 0.22/0.53  fof(f219,plain,(
% 0.22/0.53    spl3_21 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~spl3_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f172])).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    spl3_17 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.53  fof(f222,plain,(
% 0.22/0.53    ~spl3_21 | spl3_9 | ~spl3_14 | ~spl3_19),
% 0.22/0.53    inference(avatar_split_clause,[],[f217,f192,f149,f118,f219])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    spl3_9 <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k11_relat_1(sK2,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    spl3_14 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    spl3_19 <=> k2_relat_1(sK2) = k11_relat_1(sK2,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.53  fof(f217,plain,(
% 0.22/0.53    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | (spl3_9 | ~spl3_14 | ~spl3_19)),
% 0.22/0.53    inference(forward_demodulation,[],[f208,f194])).
% 0.22/0.53  fof(f194,plain,(
% 0.22/0.53    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) | ~spl3_19),
% 0.22/0.53    inference(avatar_component_clause,[],[f192])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    k11_relat_1(sK2,sK0) != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | (spl3_9 | ~spl3_14)),
% 0.22/0.53    inference(forward_demodulation,[],[f120,f151])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | ~spl3_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f149])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k11_relat_1(sK2,sK0) | spl3_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f118])).
% 0.22/0.53  fof(f210,plain,(
% 0.22/0.53    ~spl3_5 | ~spl3_10 | spl3_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f145,f140,f124,f95])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    spl3_5 <=> v1_relat_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    spl3_10 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    k1_xboole_0 != k2_relat_1(sK2) | ~v1_relat_1(sK2) | spl3_13),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f144])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_relat_1(sK2) | ~v1_relat_1(sK2) | spl3_13),
% 0.22/0.53    inference(superposition,[],[f142,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    k1_xboole_0 != k1_relat_1(sK2) | spl3_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f140])).
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    spl3_8 | ~spl3_5 | spl3_10 | ~spl3_19),
% 0.22/0.53    inference(avatar_split_clause,[],[f201,f192,f124,f95,f114])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    spl3_8 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(sK0,k1_relat_1(sK2)) | ~spl3_19),
% 0.22/0.53    inference(superposition,[],[f194,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1) | r2_hidden(X0,k1_relat_1(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 0.22/0.53  fof(f195,plain,(
% 0.22/0.53    ~spl3_5 | spl3_19 | ~spl3_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f189,f149,f192,f95])).
% 0.22/0.53  fof(f189,plain,(
% 0.22/0.53    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | ~spl3_14),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f188])).
% 0.22/0.53  fof(f188,plain,(
% 0.22/0.53    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_14),
% 0.22/0.53    inference(superposition,[],[f39,f157])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    ( ! [X0] : (k11_relat_1(X0,sK0) = k9_relat_1(X0,k1_relat_1(sK2)) | ~v1_relat_1(X0)) ) | ~spl3_14),
% 0.22/0.53    inference(superposition,[],[f64,f151])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f42,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f38,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f45,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    spl3_17 | ~spl3_4 | ~spl3_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f155,f149,f87,f172])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | (~spl3_4 | ~spl3_14)),
% 0.22/0.53    inference(backward_demodulation,[],[f89,f151])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl3_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f87])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    ~spl3_15 | ~spl3_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f158,f149,f160])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    ~v1_xboole_0(k1_relat_1(sK2)) | ~spl3_14),
% 0.22/0.53    inference(superposition,[],[f63,f151])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f37,f59])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    ~spl3_4 | spl3_14 | ~spl3_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f146,f135,f149,f87])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    spl3_12 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl3_12),
% 0.22/0.53    inference(superposition,[],[f137,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~spl3_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f135])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    ~spl3_3 | spl3_12 | spl3_2 | ~spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f92,f87,f77,f135,f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    spl3_3 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl3_2 <=> k1_xboole_0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl3_4),
% 0.22/0.53    inference(resolution,[],[f89,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(flattening,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    ~spl3_5 | ~spl3_8 | ~spl3_1 | ~spl3_9 | spl3_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f112,f104,f118,f72,f114,f95])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    spl3_1 <=> v1_funct_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    spl3_7 <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k11_relat_1(sK2,sK0) | ~v1_funct_1(sK2) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | spl3_7),
% 0.22/0.53    inference(superposition,[],[f106,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f48,f59])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) | spl3_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f104])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    spl3_6),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f108])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    $false | spl3_6),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f44,f101])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ~v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | spl3_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    spl3_6 <=> v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    ~spl3_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f60,f104])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 0.22/0.53    inference(definition_unfolding,[],[f35,f59,f59])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.22/0.53    inference(flattening,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.22/0.53    inference(negated_conjecture,[],[f16])).
% 0.22/0.53  fof(f16,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    spl3_5 | ~spl3_6 | ~spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f93,f87,f99,f95])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ~v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | v1_relat_1(sK2) | ~spl3_4),
% 0.22/0.53    inference(resolution,[],[f89,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f61,f87])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.22/0.53    inference(definition_unfolding,[],[f33,f59])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f62,f82])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.22/0.53    inference(definition_unfolding,[],[f32,f59])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ~spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f34,f77])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    k1_xboole_0 != sK1),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f31,f72])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    v1_funct_1(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (15638)------------------------------
% 0.22/0.53  % (15638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15638)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (15638)Memory used [KB]: 10874
% 0.22/0.53  % (15638)Time elapsed: 0.065 s
% 0.22/0.53  % (15638)------------------------------
% 0.22/0.53  % (15638)------------------------------
% 0.22/0.54  % (15614)Success in time 0.163 s
%------------------------------------------------------------------------------
