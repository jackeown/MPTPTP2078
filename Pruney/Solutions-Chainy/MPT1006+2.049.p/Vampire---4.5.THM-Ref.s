%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 471 expanded)
%              Number of leaves         :   26 ( 155 expanded)
%              Depth                    :   10
%              Number of atoms          :  310 (1054 expanded)
%              Number of equality atoms :   87 ( 461 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f212,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f73,f90,f95,f109,f120,f126,f138,f144,f151,f167,f193,f195,f197,f200,f203,f205,f207])).

fof(f207,plain,
    ( ~ spl4_3
    | spl4_7
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | ~ spl4_3
    | spl4_7
    | spl4_13 ),
    inference(subsumption_resolution,[],[f191,f47])).

fof(f47,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f191,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl4_3
    | spl4_7
    | spl4_13 ),
    inference(backward_demodulation,[],[f161,f183])).

fof(f183,plain,
    ( ! [X1] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X1)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f182,f111])).

fof(f111,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f110,f62])).

fof(f62,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f110,plain,(
    ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f35,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f182,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k1_xboole_0) = k10_relat_1(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f179,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] : k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2) ),
    inference(unit_resulting_resolution,[],[f35,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f179,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k1_xboole_0) = k8_relset_1(X0,X1,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f35,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f161,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1)))
    | spl4_7
    | spl4_13 ),
    inference(forward_demodulation,[],[f153,f127])).

fof(f153,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1)))
    | spl4_7
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f94,f150,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f150,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_13
  <=> k1_xboole_0 = k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f94,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_7
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f205,plain,
    ( ~ spl4_3
    | spl4_7
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl4_3
    | spl4_7
    | spl4_13 ),
    inference(subsumption_resolution,[],[f190,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f190,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_3
    | spl4_7
    | spl4_13 ),
    inference(backward_demodulation,[],[f160,f183])).

fof(f160,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1)),k10_relat_1(k1_xboole_0,sK1))
    | spl4_7
    | spl4_13 ),
    inference(forward_demodulation,[],[f156,f127])).

fof(f156,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1)),k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1))
    | spl4_7
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f94,f150,f37])).

fof(f203,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | spl4_13 ),
    inference(subsumption_resolution,[],[f201,f76])).

fof(f76,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f52,f35,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f52,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f201,plain,
    ( r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
    | ~ spl4_3
    | spl4_13 ),
    inference(forward_demodulation,[],[f189,f46])).

fof(f189,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl4_3
    | spl4_13 ),
    inference(backward_demodulation,[],[f159,f183])).

fof(f159,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1))),k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1)))
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f150,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f200,plain,
    ( ~ spl4_3
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl4_3
    | spl4_13 ),
    inference(subsumption_resolution,[],[f198,f47])).

fof(f198,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | spl4_13 ),
    inference(forward_demodulation,[],[f188,f46])).

fof(f188,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl4_3
    | spl4_13 ),
    inference(backward_demodulation,[],[f157,f183])).

fof(f157,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1)),k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1)))
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f150,f150,f37])).

fof(f197,plain,
    ( ~ spl4_3
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl4_3
    | spl4_13 ),
    inference(subsumption_resolution,[],[f187,f47])).

fof(f187,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | spl4_13 ),
    inference(backward_demodulation,[],[f150,f183])).

fof(f195,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f186,f76])).

fof(f186,plain,
    ( r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f143,f183])).

fof(f143,plain,
    ( r2_hidden(sK3(k10_relat_1(k1_xboole_0,sK1)),k10_relat_1(k1_xboole_0,sK1))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl4_12
  <=> r2_hidden(sK3(k10_relat_1(k1_xboole_0,sK1)),k10_relat_1(k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f193,plain,
    ( ~ spl4_3
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl4_3
    | spl4_11 ),
    inference(subsumption_resolution,[],[f185,f35])).

fof(f185,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_3
    | spl4_11 ),
    inference(backward_demodulation,[],[f137,f183])).

fof(f137,plain,
    ( ~ m1_subset_1(k10_relat_1(k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl4_11
  <=> m1_subset_1(k10_relat_1(k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f167,plain,
    ( ~ spl4_14
    | spl4_7 ),
    inference(avatar_split_clause,[],[f162,f92,f164])).

fof(f164,plain,
    ( spl4_14
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f162,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | spl4_7 ),
    inference(superposition,[],[f94,f127])).

fof(f151,plain,
    ( ~ spl4_13
    | spl4_10 ),
    inference(avatar_split_clause,[],[f131,f123,f148])).

fof(f123,plain,
    ( spl4_10
  <=> k1_xboole_0 = k2_zfmisc_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f131,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1))
    | spl4_10 ),
    inference(backward_demodulation,[],[f125,f127])).

fof(f125,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f144,plain,
    ( spl4_12
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f133,f106,f141])).

fof(f106,plain,
    ( spl4_8
  <=> r2_hidden(sK3(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f133,plain,
    ( r2_hidden(sK3(k10_relat_1(k1_xboole_0,sK1)),k10_relat_1(k1_xboole_0,sK1))
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f108,f127])).

fof(f108,plain,
    ( r2_hidden(sK3(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f138,plain,
    ( ~ spl4_11
    | spl4_9 ),
    inference(avatar_split_clause,[],[f132,f117,f135])).

fof(f117,plain,
    ( spl4_9
  <=> m1_subset_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f132,plain,
    ( ~ m1_subset_1(k10_relat_1(k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0))
    | spl4_9 ),
    inference(backward_demodulation,[],[f119,f127])).

fof(f119,plain,
    ( ~ m1_subset_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f126,plain,
    ( ~ spl4_10
    | spl4_7 ),
    inference(avatar_split_clause,[],[f100,f92,f123])).

fof(f100,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1))
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f94,f94,f37])).

fof(f120,plain,
    ( ~ spl4_9
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f115,f106,f50,f117])).

fof(f115,plain,
    ( ~ m1_subset_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f52,f108,f44])).

fof(f109,plain,
    ( spl4_8
    | ~ spl4_1
    | ~ spl4_2
    | spl4_5 ),
    inference(avatar_split_clause,[],[f81,f70,f55,f50,f106])).

fof(f55,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f70,plain,
    ( spl4_5
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f81,plain,
    ( r2_hidden(sK3(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1))
    | ~ spl4_1
    | ~ spl4_2
    | spl4_5 ),
    inference(backward_demodulation,[],[f74,f78])).

fof(f78,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f75,f36])).

fof(f75,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f52,f57,f44])).

fof(f57,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f74,plain,
    ( r2_hidden(sK3(k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),k8_relset_1(k1_xboole_0,sK0,sK2,sK1))
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f72,f36])).

fof(f72,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f95,plain,
    ( ~ spl4_7
    | ~ spl4_1
    | ~ spl4_2
    | spl4_5 ),
    inference(avatar_split_clause,[],[f82,f70,f55,f50,f92])).

fof(f82,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_5 ),
    inference(backward_demodulation,[],[f72,f78])).

fof(f90,plain,
    ( spl4_6
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f78,f55,f50,f87])).

fof(f87,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f73,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f31,f70])).

fof(f31,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

fof(f68,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f34,f65])).

fof(f65,plain,
    ( spl4_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f34,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f63,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f33,f60])).

fof(f33,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f58,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f48,f55])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f30,f47])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f32,f50])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:18:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (6790)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (6784)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (6784)Refutation not found, incomplete strategy% (6784)------------------------------
% 0.20/0.47  % (6784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (6784)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (6784)Memory used [KB]: 10618
% 0.20/0.47  % (6784)Time elapsed: 0.062 s
% 0.20/0.47  % (6784)------------------------------
% 0.20/0.47  % (6784)------------------------------
% 0.20/0.47  % (6790)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f212,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f73,f90,f95,f109,f120,f126,f138,f144,f151,f167,f193,f195,f197,f200,f203,f205,f207])).
% 0.20/0.47  fof(f207,plain,(
% 0.20/0.47    ~spl4_3 | spl4_7 | spl4_13),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f206])).
% 0.20/0.47  fof(f206,plain,(
% 0.20/0.47    $false | (~spl4_3 | spl4_7 | spl4_13)),
% 0.20/0.47    inference(subsumption_resolution,[],[f191,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.47    inference(equality_resolution,[],[f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.47    inference(flattening,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.47  fof(f191,plain,(
% 0.20/0.47    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | (~spl4_3 | spl4_7 | spl4_13)),
% 0.20/0.47    inference(backward_demodulation,[],[f161,f183])).
% 0.20/0.47  fof(f183,plain,(
% 0.20/0.47    ( ! [X1] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X1)) ) | ~spl4_3),
% 0.20/0.47    inference(forward_demodulation,[],[f182,f111])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | ~spl4_3),
% 0.20/0.47    inference(forward_demodulation,[],[f110,f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f60])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    spl4_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f35,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.47  fof(f182,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) = k10_relat_1(k1_xboole_0,X1)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f179,f127])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2)) )),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f35,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.47  fof(f179,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) = k8_relset_1(X0,X1,k1_xboole_0,X1)) )),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f35,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    k1_xboole_0 != k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1))) | (spl4_7 | spl4_13)),
% 0.20/0.47    inference(forward_demodulation,[],[f153,f127])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    k1_xboole_0 != k2_zfmisc_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1))) | (spl4_7 | spl4_13)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f94,f150,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    k1_xboole_0 != k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1)) | spl4_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f148])).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    spl4_13 <=> k1_xboole_0 = k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | spl4_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f92])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    spl4_7 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.47  fof(f205,plain,(
% 0.20/0.47    ~spl4_3 | spl4_7 | spl4_13),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f204])).
% 0.20/0.47  fof(f204,plain,(
% 0.20/0.47    $false | (~spl4_3 | spl4_7 | spl4_13)),
% 0.20/0.47    inference(subsumption_resolution,[],[f190,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f190,plain,(
% 0.20/0.47    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl4_3 | spl4_7 | spl4_13)),
% 0.20/0.47    inference(backward_demodulation,[],[f160,f183])).
% 0.20/0.47  fof(f160,plain,(
% 0.20/0.47    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1)),k10_relat_1(k1_xboole_0,sK1)) | (spl4_7 | spl4_13)),
% 0.20/0.47    inference(forward_demodulation,[],[f156,f127])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1)),k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)) | (spl4_7 | spl4_13)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f94,f150,f37])).
% 0.20/0.47  fof(f203,plain,(
% 0.20/0.47    ~spl4_1 | ~spl4_3 | spl4_13),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f202])).
% 0.20/0.47  fof(f202,plain,(
% 0.20/0.47    $false | (~spl4_1 | ~spl4_3 | spl4_13)),
% 0.20/0.47    inference(subsumption_resolution,[],[f201,f76])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl4_1),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f52,f35,f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0) | ~spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    spl4_1 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.47  fof(f201,plain,(
% 0.20/0.47    r2_hidden(sK3(k1_xboole_0),k1_xboole_0) | (~spl4_3 | spl4_13)),
% 0.20/0.47    inference(forward_demodulation,[],[f189,f46])).
% 0.20/0.47  fof(f189,plain,(
% 0.20/0.47    r2_hidden(sK3(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | (~spl4_3 | spl4_13)),
% 0.20/0.47    inference(backward_demodulation,[],[f159,f183])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    r2_hidden(sK3(k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1))),k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1))) | spl4_13),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f150,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.47    inference(ennf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.47    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.20/0.47  fof(f200,plain,(
% 0.20/0.47    ~spl4_3 | spl4_13),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f199])).
% 0.20/0.47  fof(f199,plain,(
% 0.20/0.47    $false | (~spl4_3 | spl4_13)),
% 0.20/0.47    inference(subsumption_resolution,[],[f198,f47])).
% 0.20/0.47  fof(f198,plain,(
% 0.20/0.47    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | (~spl4_3 | spl4_13)),
% 0.20/0.47    inference(forward_demodulation,[],[f188,f46])).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | (~spl4_3 | spl4_13)),
% 0.20/0.47    inference(backward_demodulation,[],[f157,f183])).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1)),k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1))) | spl4_13),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f150,f150,f37])).
% 0.20/0.47  fof(f197,plain,(
% 0.20/0.47    ~spl4_3 | spl4_13),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f196])).
% 0.20/0.47  fof(f196,plain,(
% 0.20/0.47    $false | (~spl4_3 | spl4_13)),
% 0.20/0.47    inference(subsumption_resolution,[],[f187,f47])).
% 0.20/0.47  fof(f187,plain,(
% 0.20/0.47    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | (~spl4_3 | spl4_13)),
% 0.20/0.47    inference(backward_demodulation,[],[f150,f183])).
% 0.20/0.47  fof(f195,plain,(
% 0.20/0.47    ~spl4_1 | ~spl4_3 | ~spl4_12),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f194])).
% 0.20/0.47  fof(f194,plain,(
% 0.20/0.47    $false | (~spl4_1 | ~spl4_3 | ~spl4_12)),
% 0.20/0.47    inference(subsumption_resolution,[],[f186,f76])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    r2_hidden(sK3(k1_xboole_0),k1_xboole_0) | (~spl4_3 | ~spl4_12)),
% 0.20/0.47    inference(backward_demodulation,[],[f143,f183])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    r2_hidden(sK3(k10_relat_1(k1_xboole_0,sK1)),k10_relat_1(k1_xboole_0,sK1)) | ~spl4_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f141])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    spl4_12 <=> r2_hidden(sK3(k10_relat_1(k1_xboole_0,sK1)),k10_relat_1(k1_xboole_0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.47  fof(f193,plain,(
% 0.20/0.47    ~spl4_3 | spl4_11),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f192])).
% 0.20/0.47  fof(f192,plain,(
% 0.20/0.47    $false | (~spl4_3 | spl4_11)),
% 0.20/0.47    inference(subsumption_resolution,[],[f185,f35])).
% 0.20/0.47  fof(f185,plain,(
% 0.20/0.47    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_3 | spl4_11)),
% 0.20/0.47    inference(backward_demodulation,[],[f137,f183])).
% 0.20/0.47  fof(f137,plain,(
% 0.20/0.47    ~m1_subset_1(k10_relat_1(k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0)) | spl4_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f135])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    spl4_11 <=> m1_subset_1(k10_relat_1(k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.47  fof(f167,plain,(
% 0.20/0.47    ~spl4_14 | spl4_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f162,f92,f164])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    spl4_14 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | spl4_7),
% 0.20/0.47    inference(superposition,[],[f94,f127])).
% 0.20/0.47  fof(f151,plain,(
% 0.20/0.47    ~spl4_13 | spl4_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f131,f123,f148])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    spl4_10 <=> k1_xboole_0 = k2_zfmisc_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    k1_xboole_0 != k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK1),k10_relat_1(k1_xboole_0,sK1)) | spl4_10),
% 0.20/0.47    inference(backward_demodulation,[],[f125,f127])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    k1_xboole_0 != k2_zfmisc_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)) | spl4_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f123])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    spl4_12 | ~spl4_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f133,f106,f141])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    spl4_8 <=> r2_hidden(sK3(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    r2_hidden(sK3(k10_relat_1(k1_xboole_0,sK1)),k10_relat_1(k1_xboole_0,sK1)) | ~spl4_8),
% 0.20/0.47    inference(backward_demodulation,[],[f108,f127])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    r2_hidden(sK3(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)) | ~spl4_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f106])).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    ~spl4_11 | spl4_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f132,f117,f135])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    spl4_9 <=> m1_subset_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    ~m1_subset_1(k10_relat_1(k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0)) | spl4_9),
% 0.20/0.47    inference(backward_demodulation,[],[f119,f127])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    ~m1_subset_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0)) | spl4_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f117])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    ~spl4_10 | spl4_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f100,f92,f123])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    k1_xboole_0 != k2_zfmisc_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)) | spl4_7),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f94,f94,f37])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    ~spl4_9 | ~spl4_1 | ~spl4_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f115,f106,f50,f117])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    ~m1_subset_1(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0)) | (~spl4_1 | ~spl4_8)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f52,f108,f44])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    spl4_8 | ~spl4_1 | ~spl4_2 | spl4_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f81,f70,f55,f50,f106])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    spl4_5 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    r2_hidden(sK3(k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)) | (~spl4_1 | ~spl4_2 | spl4_5)),
% 0.20/0.47    inference(backward_demodulation,[],[f74,f78])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    k1_xboole_0 = sK2 | (~spl4_1 | ~spl4_2)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f75,f36])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | (~spl4_1 | ~spl4_2)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f52,f57,f44])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f55])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    r2_hidden(sK3(k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),k8_relset_1(k1_xboole_0,sK0,sK2,sK1)) | spl4_5),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f72,f36])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl4_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f70])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    ~spl4_7 | ~spl4_1 | ~spl4_2 | spl4_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f82,f70,f55,f50,f92])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | (~spl4_1 | ~spl4_2 | spl4_5)),
% 0.20/0.47    inference(backward_demodulation,[],[f72,f78])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    spl4_6 | ~spl4_1 | ~spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f78,f55,f50,f87])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    spl4_6 <=> k1_xboole_0 = sK2),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ~spl4_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f31,f70])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.20/0.47    inference(ennf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.47    inference(pure_predicate_removal,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.47    inference(pure_predicate_removal,[],[f12])).
% 0.20/0.47  fof(f12,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.47    inference(negated_conjecture,[],[f11])).
% 0.20/0.47  fof(f11,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl4_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f34,f65])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    spl4_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    spl4_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f33,f60])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f48,f55])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.47    inference(backward_demodulation,[],[f30,f47])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    spl4_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f32,f50])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (6790)------------------------------
% 0.20/0.47  % (6790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (6790)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (6790)Memory used [KB]: 1663
% 0.20/0.47  % (6790)Time elapsed: 0.067 s
% 0.20/0.47  % (6790)------------------------------
% 0.20/0.47  % (6790)------------------------------
% 0.20/0.48  % (6782)Success in time 0.121 s
%------------------------------------------------------------------------------
