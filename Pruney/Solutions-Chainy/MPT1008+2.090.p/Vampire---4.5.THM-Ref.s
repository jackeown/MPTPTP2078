%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 236 expanded)
%              Number of leaves         :   33 (  97 expanded)
%              Depth                    :    9
%              Number of atoms          :  316 ( 542 expanded)
%              Number of equality atoms :   81 ( 184 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f230,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f107,f112,f121,f125,f135,f140,f147,f162,f175,f184,f192,f209,f219,f225,f229])).

fof(f229,plain,
    ( ~ spl3_16
    | spl3_23 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl3_16
    | spl3_23 ),
    inference(unit_resulting_resolution,[],[f174,f224,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f224,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | spl3_23 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl3_23
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f174,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl3_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f225,plain,
    ( ~ spl3_23
    | spl3_21
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f220,f216,f206,f222])).

fof(f206,plain,
    ( spl3_21
  <=> k11_relat_1(sK2,sK0) = k2_relset_1(k1_relat_1(sK2),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f216,plain,
    ( spl3_22
  <=> k2_relat_1(sK2) = k11_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f220,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | spl3_21
    | ~ spl3_22 ),
    inference(backward_demodulation,[],[f208,f218])).

fof(f218,plain,
    ( k2_relat_1(sK2) = k11_relat_1(sK2,sK0)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f216])).

fof(f208,plain,
    ( k11_relat_1(sK2,sK0) != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | spl3_21 ),
    inference(avatar_component_clause,[],[f206])).

fof(f219,plain,
    ( ~ spl3_8
    | spl3_22
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f213,f144,f216,f114])).

fof(f114,plain,
    ( spl3_8
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f144,plain,
    ( spl3_13
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f213,plain,
    ( k2_relat_1(sK2) = k11_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,
    ( k2_relat_1(sK2) = k11_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(superposition,[],[f36,f153])).

fof(f153,plain,
    ( ! [X0] :
        ( k11_relat_1(X0,sK0) = k9_relat_1(X0,k1_relat_1(sK2))
        | ~ v1_relat_1(X0) )
    | ~ spl3_13 ),
    inference(superposition,[],[f63,f146])).

fof(f146,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f144])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f37,f59])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f36,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f209,plain,
    ( ~ spl3_21
    | spl3_11
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f193,f144,f132,f206])).

fof(f132,plain,
    ( spl3_11
  <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k11_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f193,plain,
    ( k11_relat_1(sK2,sK0) != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | spl3_11
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f134,f146])).

fof(f134,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k11_relat_1(sK2,sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f192,plain,
    ( spl3_10
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl3_10
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f130,f161,f183])).

fof(f183,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | r2_hidden(sK0,X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl3_17
  <=> ! [X0] :
        ( r2_hidden(sK0,X0)
        | ~ v4_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f161,plain,
    ( v4_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl3_14
  <=> v4_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f130,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl3_10
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f184,plain,
    ( ~ spl3_8
    | spl3_17
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f168,f144,f182,f114])).

fof(f168,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,X0)
        | ~ v1_relat_1(sK2)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl3_13 ),
    inference(resolution,[],[f154,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f154,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),X1)
        | r2_hidden(sK0,X1) )
    | ~ spl3_13 ),
    inference(superposition,[],[f67,f146])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f55,f58])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f175,plain,
    ( spl3_16
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f151,f144,f89,f172])).

fof(f89,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f151,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f91,f146])).

fof(f91,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f162,plain,
    ( spl3_14
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f150,f144,f109,f159])).

fof(f109,plain,
    ( spl3_7
  <=> v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f150,plain,
    ( v4_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f111,f146])).

fof(f111,plain,
    ( v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f147,plain,
    ( ~ spl3_4
    | spl3_13
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f141,f137,f144,f89])).

fof(f137,plain,
    ( spl3_12
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f141,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl3_12 ),
    inference(superposition,[],[f139,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f139,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f140,plain,
    ( ~ spl3_3
    | spl3_12
    | spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f94,f89,f79,f137,f84])).

fof(f84,plain,
    ( spl3_3
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f79,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f94,plain,
    ( k1_xboole_0 = sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f91,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f135,plain,
    ( ~ spl3_8
    | ~ spl3_10
    | ~ spl3_1
    | ~ spl3_11
    | spl3_6 ),
    inference(avatar_split_clause,[],[f126,f104,f132,f74,f128,f114])).

fof(f74,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f104,plain,
    ( spl3_6
  <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f126,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k11_relat_1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl3_6 ),
    inference(superposition,[],[f106,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f43,f59])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f106,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f125,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl3_9 ),
    inference(unit_resulting_resolution,[],[f39,f120])).

fof(f120,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl3_9
  <=> v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f121,plain,
    ( spl3_8
    | ~ spl3_9
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f97,f89,f118,f114])).

fof(f97,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f91,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f112,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f95,f89,f109])).

fof(f95,plain,
    ( v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl3_4 ),
    inference(resolution,[],[f91,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f107,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f60,f104])).

fof(f60,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f34,f59,f59])).

fof(f34,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f92,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f61,f89])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f32,f59])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f87,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f62,f84])).

fof(f62,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f31,f59])).

fof(f31,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f82,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f33,f79])).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f30,f74])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:35:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (5895)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (5887)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (5879)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (5895)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (5878)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f230,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f107,f112,f121,f125,f135,f140,f147,f162,f175,f184,f192,f209,f219,f225,f229])).
% 0.21/0.53  fof(f229,plain,(
% 0.21/0.53    ~spl3_16 | spl3_23),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f226])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    $false | (~spl3_16 | spl3_23)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f174,f224,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.53  fof(f224,plain,(
% 0.21/0.53    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | spl3_23),
% 0.21/0.53    inference(avatar_component_clause,[],[f222])).
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    spl3_23 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK1,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~spl3_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f172])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    spl3_16 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.53  fof(f225,plain,(
% 0.21/0.53    ~spl3_23 | spl3_21 | ~spl3_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f220,f216,f206,f222])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    spl3_21 <=> k11_relat_1(sK2,sK0) = k2_relset_1(k1_relat_1(sK2),sK1,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    spl3_22 <=> k2_relat_1(sK2) = k11_relat_1(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | (spl3_21 | ~spl3_22)),
% 0.21/0.53    inference(backward_demodulation,[],[f208,f218])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) | ~spl3_22),
% 0.21/0.53    inference(avatar_component_clause,[],[f216])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    k11_relat_1(sK2,sK0) != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | spl3_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f206])).
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    ~spl3_8 | spl3_22 | ~spl3_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f213,f144,f216,f114])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    spl3_8 <=> v1_relat_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    spl3_13 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | ~spl3_13),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f212])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_13),
% 0.21/0.53    inference(superposition,[],[f36,f153])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    ( ! [X0] : (k11_relat_1(X0,sK0) = k9_relat_1(X0,k1_relat_1(sK2)) | ~v1_relat_1(X0)) ) | ~spl3_13),
% 0.21/0.53    inference(superposition,[],[f63,f146])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | ~spl3_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f144])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f37,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f35,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f40,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    ~spl3_21 | spl3_11 | ~spl3_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f193,f144,f132,f206])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    spl3_11 <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k11_relat_1(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    k11_relat_1(sK2,sK0) != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | (spl3_11 | ~spl3_13)),
% 0.21/0.53    inference(forward_demodulation,[],[f134,f146])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k11_relat_1(sK2,sK0) | spl3_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f132])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    spl3_10 | ~spl3_14 | ~spl3_17),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f190])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    $false | (spl3_10 | ~spl3_14 | ~spl3_17)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f130,f161,f183])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    ( ! [X0] : (~v4_relat_1(sK2,X0) | r2_hidden(sK0,X0)) ) | ~spl3_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f182])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    spl3_17 <=> ! [X0] : (r2_hidden(sK0,X0) | ~v4_relat_1(sK2,X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    v4_relat_1(sK2,k1_relat_1(sK2)) | ~spl3_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f159])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    spl3_14 <=> v4_relat_1(sK2,k1_relat_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl3_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f128])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    spl3_10 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    ~spl3_8 | spl3_17 | ~spl3_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f168,f144,f182,f114])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK0,X0) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,X0)) ) | ~spl3_13),
% 0.21/0.53    inference(resolution,[],[f154,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | r2_hidden(sK0,X1)) ) | ~spl3_13),
% 0.21/0.53    inference(superposition,[],[f67,f146])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f55,f58])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    spl3_16 | ~spl3_4 | ~spl3_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f151,f144,f89,f172])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | (~spl3_4 | ~spl3_13)),
% 0.21/0.53    inference(backward_demodulation,[],[f91,f146])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl3_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f89])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    spl3_14 | ~spl3_7 | ~spl3_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f150,f144,f109,f159])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    spl3_7 <=> v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    v4_relat_1(sK2,k1_relat_1(sK2)) | (~spl3_7 | ~spl3_13)),
% 0.21/0.53    inference(backward_demodulation,[],[f111,f146])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl3_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f109])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    ~spl3_4 | spl3_13 | ~spl3_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f141,f137,f144,f89])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    spl3_12 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl3_12),
% 0.21/0.53    inference(superposition,[],[f139,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~spl3_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f137])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    ~spl3_3 | spl3_12 | spl3_2 | ~spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f94,f89,f79,f137,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    spl3_3 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    spl3_2 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl3_4),
% 0.21/0.53    inference(resolution,[],[f91,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(flattening,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    ~spl3_8 | ~spl3_10 | ~spl3_1 | ~spl3_11 | spl3_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f126,f104,f132,f74,f128,f114])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    spl3_1 <=> v1_funct_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    spl3_6 <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k11_relat_1(sK2,sK0) | ~v1_funct_1(sK2) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | spl3_6),
% 0.21/0.53    inference(superposition,[],[f106,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f43,f59])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) | spl3_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f104])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    spl3_9),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f122])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    $false | spl3_9),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f39,f120])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ~v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | spl3_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f118])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    spl3_9 <=> v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    spl3_8 | ~spl3_9 | ~spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f97,f89,f118,f114])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ~v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | v1_relat_1(sK2) | ~spl3_4),
% 0.21/0.53    inference(resolution,[],[f91,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    spl3_7 | ~spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f95,f89,f109])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl3_4),
% 0.21/0.53    inference(resolution,[],[f91,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ~spl3_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f60,f104])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 0.21/0.53    inference(definition_unfolding,[],[f34,f59,f59])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.21/0.53    inference(negated_conjecture,[],[f15])).
% 0.21/0.53  fof(f15,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f61,f89])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.53    inference(definition_unfolding,[],[f32,f59])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f62,f84])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.53    inference(definition_unfolding,[],[f31,f59])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ~spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f33,f79])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    k1_xboole_0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f30,f74])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    v1_funct_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (5895)------------------------------
% 0.21/0.53  % (5895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5895)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (5895)Memory used [KB]: 10874
% 0.21/0.53  % (5895)Time elapsed: 0.069 s
% 0.21/0.53  % (5895)------------------------------
% 0.21/0.53  % (5895)------------------------------
% 0.21/0.54  % (5871)Success in time 0.166 s
%------------------------------------------------------------------------------
