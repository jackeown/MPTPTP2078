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
% DateTime   : Thu Dec  3 13:03:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 145 expanded)
%              Number of leaves         :   24 (  66 expanded)
%              Depth                    :    7
%              Number of atoms          :  237 ( 376 expanded)
%              Number of equality atoms :   63 ( 106 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f54,f66,f70,f78,f87,f93,f107,f120,f124,f132,f139,f147,f155,f161,f165])).

fof(f165,plain,
    ( ~ spl3_8
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl3_8
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f163,f106])).

fof(f106,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_16
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f163,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_8
    | ~ spl3_26 ),
    inference(superposition,[],[f160,f65])).

fof(f65,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_8
  <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f160,plain,
    ( ! [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl3_26
  <=> ! [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f161,plain,
    ( spl3_26
    | ~ spl3_5
    | spl3_23
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f157,f153,f137,f52,f159])).

fof(f52,plain,
    ( spl3_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f137,plain,
    ( spl3_23
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f153,plain,
    ( spl3_25
  <=> ! [X3,X5,X4] :
        ( k1_relat_1(X5) = k10_relat_1(X5,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f157,plain,
    ( ! [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl3_5
    | spl3_23
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f156,f53])).

fof(f53,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f156,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
    | spl3_23
    | ~ spl3_25 ),
    inference(superposition,[],[f138,f154])).

fof(f154,plain,
    ( ! [X4,X5,X3] :
        ( k1_relat_1(X5) = k10_relat_1(X5,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f153])).

fof(f138,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | spl3_23 ),
    inference(avatar_component_clause,[],[f137])).

fof(f155,plain,
    ( spl3_25
    | ~ spl3_14
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f151,f145,f91,f153])).

fof(f91,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f145,plain,
    ( spl3_24
  <=> ! [X1,X0,X2] :
        ( k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f151,plain,
    ( ! [X4,X5,X3] :
        ( k1_relat_1(X5) = k10_relat_1(X5,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
    | ~ spl3_14
    | ~ spl3_24 ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,
    ( ! [X4,X5,X3] :
        ( k1_relat_1(X5) = k10_relat_1(X5,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
    | ~ spl3_14
    | ~ spl3_24 ),
    inference(superposition,[],[f146,f92])).

fof(f92,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f145])).

fof(f147,plain,
    ( spl3_24
    | ~ spl3_20
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f143,f130,f122,f145])).

fof(f122,plain,
    ( spl3_20
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f130,plain,
    ( spl3_22
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f143,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_20
    | ~ spl3_22 ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_20
    | ~ spl3_22 ),
    inference(superposition,[],[f131,f123])).

fof(f123,plain,
    ( ! [X2,X0,X3,X1] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f122])).

fof(f131,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f130])).

fof(f139,plain,
    ( ~ spl3_23
    | ~ spl3_8
    | ~ spl3_16
    | spl3_19
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f135,f122,f118,f105,f64,f137])).

fof(f118,plain,
    ( spl3_19
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f135,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | ~ spl3_8
    | ~ spl3_16
    | spl3_19
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f134,f106])).

fof(f134,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | ~ spl3_8
    | spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f133,f65])).

fof(f133,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_19
    | ~ spl3_20 ),
    inference(superposition,[],[f119,f123])).

fof(f119,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl3_19 ),
    inference(avatar_component_clause,[],[f118])).

fof(f132,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f30,f130])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f124,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f31,f122])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f120,plain,
    ( ~ spl3_19
    | ~ spl3_3
    | spl3_4
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f96,f85,f48,f44,f118])).

fof(f44,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f48,plain,
    ( spl3_4
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f85,plain,
    ( spl3_13
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f96,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | ~ spl3_3
    | spl3_4
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f49,f94])).

fof(f94,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(resolution,[],[f86,f45])).

fof(f45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f49,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f107,plain,
    ( spl3_16
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f97,f85,f44,f105])).

fof(f97,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f45,f94])).

fof(f93,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f28,f91])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f87,plain,
    ( spl3_13
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f79,f76,f68,f85])).

fof(f68,plain,
    ( spl3_9
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f76,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(resolution,[],[f77,f69])).

fof(f69,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f78,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f24,f76])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f70,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f22,f68])).

fof(f22,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f66,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f33,f64])).

fof(f33,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f54,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f52])).

fof(f20,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f50,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f19,f48])).

fof(f19,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

fof(f46,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f34,f44])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f18,f33])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:57:15 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.47  % (29673)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (29669)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (29669)Refutation not found, incomplete strategy% (29669)------------------------------
% 0.22/0.48  % (29669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (29669)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (29669)Memory used [KB]: 10618
% 0.22/0.48  % (29669)Time elapsed: 0.059 s
% 0.22/0.48  % (29669)------------------------------
% 0.22/0.48  % (29669)------------------------------
% 0.22/0.48  % (29686)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.48  % (29677)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (29683)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (29670)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (29677)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f46,f50,f54,f66,f70,f78,f87,f93,f107,f120,f124,f132,f139,f147,f155,f161,f165])).
% 0.22/0.49  fof(f165,plain,(
% 0.22/0.49    ~spl3_8 | ~spl3_16 | ~spl3_26),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f164])).
% 0.22/0.49  fof(f164,plain,(
% 0.22/0.49    $false | (~spl3_8 | ~spl3_16 | ~spl3_26)),
% 0.22/0.49    inference(subsumption_resolution,[],[f163,f106])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl3_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f105])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    spl3_16 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.49  fof(f163,plain,(
% 0.22/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_8 | ~spl3_26)),
% 0.22/0.49    inference(superposition,[],[f160,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) ) | ~spl3_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    spl3_8 <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | ~spl3_26),
% 0.22/0.49    inference(avatar_component_clause,[],[f159])).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    spl3_26 <=> ! [X0] : ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    spl3_26 | ~spl3_5 | spl3_23 | ~spl3_25),
% 0.22/0.49    inference(avatar_split_clause,[],[f157,f153,f137,f52,f159])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    spl3_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    spl3_23 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    spl3_25 <=> ! [X3,X5,X4] : (k1_relat_1(X5) = k10_relat_1(X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (~spl3_5 | spl3_23 | ~spl3_25)),
% 0.22/0.49    inference(subsumption_resolution,[],[f156,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f52])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (spl3_23 | ~spl3_25)),
% 0.22/0.49    inference(superposition,[],[f138,f154])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (k1_relat_1(X5) = k10_relat_1(X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | ~spl3_25),
% 0.22/0.49    inference(avatar_component_clause,[],[f153])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | spl3_23),
% 0.22/0.49    inference(avatar_component_clause,[],[f137])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    spl3_25 | ~spl3_14 | ~spl3_24),
% 0.22/0.49    inference(avatar_split_clause,[],[f151,f145,f91,f153])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    spl3_14 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    spl3_24 <=> ! [X1,X0,X2] : (k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (k1_relat_1(X5) = k10_relat_1(X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | (~spl3_14 | ~spl3_24)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f148])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (k1_relat_1(X5) = k10_relat_1(X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | (~spl3_14 | ~spl3_24)),
% 0.22/0.49    inference(superposition,[],[f146,f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f91])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f145])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    spl3_24 | ~spl3_20 | ~spl3_22),
% 0.22/0.49    inference(avatar_split_clause,[],[f143,f130,f122,f145])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    spl3_20 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    spl3_22 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl3_20 | ~spl3_22)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f140])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl3_20 | ~spl3_22)),
% 0.22/0.49    inference(superposition,[],[f131,f123])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f122])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f130])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    ~spl3_23 | ~spl3_8 | ~spl3_16 | spl3_19 | ~spl3_20),
% 0.22/0.49    inference(avatar_split_clause,[],[f135,f122,f118,f105,f64,f137])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    spl3_19 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | (~spl3_8 | ~spl3_16 | spl3_19 | ~spl3_20)),
% 0.22/0.49    inference(subsumption_resolution,[],[f134,f106])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | (~spl3_8 | spl3_19 | ~spl3_20)),
% 0.22/0.49    inference(forward_demodulation,[],[f133,f65])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_19 | ~spl3_20)),
% 0.22/0.49    inference(superposition,[],[f119,f123])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | spl3_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f118])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    spl3_22),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f130])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    spl3_20),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f122])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    ~spl3_19 | ~spl3_3 | spl3_4 | ~spl3_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f96,f85,f48,f44,f118])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    spl3_4 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl3_13 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | (~spl3_3 | spl3_4 | ~spl3_13)),
% 0.22/0.49    inference(backward_demodulation,[],[f49,f94])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    k1_xboole_0 = sK2 | (~spl3_3 | ~spl3_13)),
% 0.22/0.49    inference(resolution,[],[f86,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f44])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl3_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f85])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f48])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    spl3_16 | ~spl3_3 | ~spl3_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f97,f85,f44,f105])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_3 | ~spl3_13)),
% 0.22/0.49    inference(backward_demodulation,[],[f45,f94])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    spl3_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f28,f91])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    spl3_13 | ~spl3_9 | ~spl3_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f79,f76,f68,f85])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    spl3_9 <=> ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    spl3_11 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | (~spl3_9 | ~spl3_11)),
% 0.22/0.49    inference(resolution,[],[f77,f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl3_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f68])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl3_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f76])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    spl3_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f24,f76])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    spl3_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f22,f68])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    spl3_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f64])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.49    inference(equality_resolution,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f20,f52])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ~spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f19,f48])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 0.22/0.49    inference(flattening,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.49    inference(negated_conjecture,[],[f8])).
% 0.22/0.49  fof(f8,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f44])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.49    inference(backward_demodulation,[],[f18,f33])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (29677)------------------------------
% 0.22/0.49  % (29677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (29677)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (29677)Memory used [KB]: 10618
% 0.22/0.49  % (29677)Time elapsed: 0.076 s
% 0.22/0.49  % (29677)------------------------------
% 0.22/0.49  % (29677)------------------------------
% 0.22/0.49  % (29667)Success in time 0.129 s
%------------------------------------------------------------------------------
