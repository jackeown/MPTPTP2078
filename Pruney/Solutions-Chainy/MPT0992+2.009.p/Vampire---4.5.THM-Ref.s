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
% DateTime   : Thu Dec  3 13:03:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 553 expanded)
%              Number of leaves         :   34 ( 191 expanded)
%              Depth                    :   16
%              Number of atoms          :  574 (1636 expanded)
%              Number of equality atoms :   81 ( 246 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1167,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f90,f96,f107,f111,f134,f141,f148,f158,f177,f183,f265,f358,f403,f511,f617,f761,f770,f778,f807,f1007,f1163,f1166])).

fof(f1166,plain,
    ( ~ spl4_1
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_47
    | ~ spl4_54
    | spl4_60 ),
    inference(avatar_contradiction_clause,[],[f1165])).

fof(f1165,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_47
    | ~ spl4_54
    | spl4_60 ),
    inference(subsumption_resolution,[],[f1164,f1006])).

fof(f1006,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f1005])).

fof(f1005,plain,
    ( spl4_54
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f1164,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_47
    | spl4_60 ),
    inference(forward_demodulation,[],[f1162,f997])).

fof(f997,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f993,f806])).

fof(f806,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f805])).

fof(f805,plain,
    ( spl4_47
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f993,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(sK3,X0)
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(resolution,[],[f405,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f405,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f390,f77])).

fof(f77,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f390,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(superposition,[],[f308,f103])).

fof(f103,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f308,plain,
    ( ! [X12] : r1_tarski(k7_relat_1(sK3,X12),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f290,f127])).

fof(f127,plain,
    ( ! [X2] : k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f116,f85])).

fof(f85,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f116,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK3)
        | k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2) )
    | ~ spl4_7 ),
    inference(resolution,[],[f110,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f110,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f290,plain,
    ( ! [X12] : r1_tarski(k2_partfun1(sK0,sK1,sK3,X12),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f126,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f126,plain,
    ( ! [X1] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f115,f85])).

fof(f115,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK3)
        | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl4_7 ),
    inference(resolution,[],[f110,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f1162,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_60 ),
    inference(avatar_component_clause,[],[f1161])).

fof(f1161,plain,
    ( spl4_60
  <=> v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f1163,plain,
    ( ~ spl4_60
    | spl4_42
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f889,f805,f768,f1161])).

fof(f768,plain,
    ( spl4_42
  <=> v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f889,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_42
    | ~ spl4_47 ),
    inference(superposition,[],[f769,f806])).

fof(f769,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_42 ),
    inference(avatar_component_clause,[],[f768])).

fof(f1007,plain,
    ( spl4_54
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f895,f805,f105,f102,f94,f1005])).

fof(f94,plain,
    ( spl4_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f105,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f895,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f894,f103])).

fof(f894,plain,
    ( v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f832,f159])).

fof(f159,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f832,plain,
    ( v1_funct_2(k1_xboole_0,sK0,sK1)
    | ~ spl4_3
    | ~ spl4_47 ),
    inference(superposition,[],[f95,f806])).

fof(f95,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f807,plain,
    ( spl4_47
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f801,f776,f805])).

fof(f776,plain,
    ( spl4_44
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f801,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_44 ),
    inference(resolution,[],[f777,f55])).

fof(f777,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f776])).

fof(f778,plain,
    ( spl4_44
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f238,f181,f105,f776])).

fof(f181,plain,
    ( spl4_15
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f238,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f233,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f233,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(superposition,[],[f182,f159])).

fof(f182,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f181])).

fof(f770,plain,
    ( ~ spl4_42
    | ~ spl4_6
    | ~ spl4_25
    | spl4_36 ),
    inference(avatar_split_clause,[],[f763,f509,f263,f105,f768])).

fof(f263,plain,
    ( spl4_25
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f509,plain,
    ( spl4_36
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f763,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_25
    | spl4_36 ),
    inference(forward_demodulation,[],[f762,f264])).

fof(f264,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f263])).

fof(f762,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)
    | ~ spl4_6
    | spl4_36 ),
    inference(forward_demodulation,[],[f760,f159])).

fof(f760,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_36 ),
    inference(avatar_component_clause,[],[f509])).

fof(f761,plain,
    ( ~ spl4_36
    | ~ spl4_1
    | ~ spl4_7
    | spl4_10 ),
    inference(avatar_split_clause,[],[f618,f139,f109,f84,f509])).

fof(f139,plain,
    ( spl4_10
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f618,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_1
    | ~ spl4_7
    | spl4_10 ),
    inference(forward_demodulation,[],[f140,f127])).

fof(f140,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f139])).

fof(f617,plain,
    ( ~ spl4_1
    | ~ spl4_7
    | spl4_11
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f616])).

fof(f616,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_7
    | spl4_11
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f610,f147])).

fof(f147,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl4_11
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f610,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_30 ),
    inference(superposition,[],[f342,f357])).

fof(f357,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl4_30
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f342,plain,
    ( ! [X2] : m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f341,f304])).

fof(f304,plain,
    ( ! [X8] : v1_relat_1(k7_relat_1(sK3,X8))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f286,f127])).

fof(f286,plain,
    ( ! [X8] : v1_relat_1(k2_partfun1(sK0,sK1,sK3,X8))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f126,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f341,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X2))
        | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1))) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f336,f280])).

fof(f280,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK3,X0))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(superposition,[],[f124,f127])).

fof(f124,plain,
    ( ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f114,f85])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) )
    | ~ spl4_7 ),
    inference(resolution,[],[f110,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f336,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(k7_relat_1(sK3,X2))
        | ~ v1_relat_1(k7_relat_1(sK3,X2))
        | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1))) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f312,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f312,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f311,f304])).

fof(f311,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
        | ~ v1_relat_1(k7_relat_1(sK3,X0)) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f306,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f306,plain,
    ( ! [X10] : v5_relat_1(k7_relat_1(sK3,X10),sK1)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f288,f127])).

fof(f288,plain,
    ( ! [X10] : v5_relat_1(k2_partfun1(sK0,sK1,sK3,X10),sK1)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f126,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f511,plain,
    ( spl4_36
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f497,f356,f109,f84,f509])).

fof(f497,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_30 ),
    inference(superposition,[],[f340,f357])).

fof(f340,plain,
    ( ! [X1] : v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f339,f304])).

fof(f339,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X1))
        | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f335,f280])).

fof(f335,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k7_relat_1(sK3,X1))
        | ~ v1_relat_1(k7_relat_1(sK3,X1))
        | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1) )
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f312,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f403,plain,
    ( ~ spl4_1
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | spl4_11
    | ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | spl4_11
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f372,f401])).

fof(f401,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f388,f77])).

fof(f388,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(superposition,[],[f291,f103])).

fof(f291,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(superposition,[],[f126,f127])).

fof(f372,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_6
    | spl4_11
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f171,f264])).

fof(f171,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_6
    | spl4_11 ),
    inference(forward_demodulation,[],[f168,f76])).

fof(f168,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ spl4_6
    | spl4_11 ),
    inference(superposition,[],[f147,f159])).

fof(f358,plain,
    ( spl4_30
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f354,f156,f132,f88,f356])).

fof(f88,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f132,plain,
    ( spl4_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f156,plain,
    ( spl4_13
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f354,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(resolution,[],[f179,f89])).

fof(f89,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f178,f133])).

fof(f133,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f132])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ v1_relat_1(sK3)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_13 ),
    inference(superposition,[],[f70,f157])).

fof(f157,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f156])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f265,plain,
    ( spl4_25
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f243,f175,f263])).

fof(f175,plain,
    ( spl4_14
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f243,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_14 ),
    inference(resolution,[],[f176,f55])).

fof(f176,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f175])).

fof(f183,plain,
    ( spl4_15
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f123,f109,f181])).

fof(f123,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_7 ),
    inference(resolution,[],[f110,f64])).

fof(f177,plain,
    ( spl4_14
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f164,f102,f88,f175])).

fof(f164,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(superposition,[],[f89,f103])).

fof(f158,plain,
    ( spl4_13
    | ~ spl4_3
    | spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f130,f109,f105,f94,f156])).

fof(f130,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_3
    | spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f120,f129])).

fof(f129,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_3
    | spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f128,f95])).

fof(f128,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f118,f106])).

fof(f106,plain,
    ( k1_xboole_0 != sK1
    | spl4_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f118,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_7 ),
    inference(resolution,[],[f110,f61])).

fof(f61,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f120,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f110,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f148,plain,
    ( ~ spl4_11
    | ~ spl4_1
    | ~ spl4_7
    | spl4_9 ),
    inference(avatar_split_clause,[],[f142,f136,f109,f84,f146])).

fof(f136,plain,
    ( spl4_9
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f142,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_1
    | ~ spl4_7
    | spl4_9 ),
    inference(forward_demodulation,[],[f137,f127])).

fof(f137,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f141,plain,
    ( ~ spl4_9
    | ~ spl4_10
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f125,f109,f84,f139,f136])).

fof(f125,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f43,f124])).

fof(f43,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f134,plain,
    ( spl4_8
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f119,f109,f132])).

fof(f119,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f110,f66])).

fof(f111,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f47,f109])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f107,plain,
    ( spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f44,f105,f102])).

fof(f44,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f96,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f46,f94])).

fof(f46,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f90,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f48,f88])).

fof(f48,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f86,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f45,f84])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:20:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (24179)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (24190)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (24184)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (24191)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (24192)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (24183)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (24178)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (24188)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.51  % (24197)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (24185)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (24195)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (24189)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (24193)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (24182)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.52  % (24194)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.52  % (24187)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (24181)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (24180)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.52  % (24186)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.53  % (24196)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.53  % (24198)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.54  % (24178)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f1167,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f86,f90,f96,f107,f111,f134,f141,f148,f158,f177,f183,f265,f358,f403,f511,f617,f761,f770,f778,f807,f1007,f1163,f1166])).
% 0.22/0.54  fof(f1166,plain,(
% 0.22/0.54    ~spl4_1 | ~spl4_5 | ~spl4_7 | ~spl4_47 | ~spl4_54 | spl4_60),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1165])).
% 0.22/0.54  fof(f1165,plain,(
% 0.22/0.54    $false | (~spl4_1 | ~spl4_5 | ~spl4_7 | ~spl4_47 | ~spl4_54 | spl4_60)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1164,f1006])).
% 0.22/0.54  fof(f1006,plain,(
% 0.22/0.54    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl4_54),
% 0.22/0.54    inference(avatar_component_clause,[],[f1005])).
% 0.22/0.54  fof(f1005,plain,(
% 0.22/0.54    spl4_54 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.22/0.54  fof(f1164,plain,(
% 0.22/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_5 | ~spl4_7 | ~spl4_47 | spl4_60)),
% 0.22/0.54    inference(forward_demodulation,[],[f1162,f997])).
% 0.22/0.54  fof(f997,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl4_1 | ~spl4_5 | ~spl4_7 | ~spl4_47)),
% 0.22/0.54    inference(forward_demodulation,[],[f993,f806])).
% 0.22/0.54  fof(f806,plain,(
% 0.22/0.54    k1_xboole_0 = sK3 | ~spl4_47),
% 0.22/0.54    inference(avatar_component_clause,[],[f805])).
% 0.22/0.54  fof(f805,plain,(
% 0.22/0.54    spl4_47 <=> k1_xboole_0 = sK3),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.22/0.54  fof(f993,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK3,X0)) ) | (~spl4_1 | ~spl4_5 | ~spl4_7)),
% 0.22/0.54    inference(resolution,[],[f405,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.54  fof(f405,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0)) ) | (~spl4_1 | ~spl4_5 | ~spl4_7)),
% 0.22/0.54    inference(forward_demodulation,[],[f390,f77])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.54  fof(f390,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(k1_xboole_0,sK1))) ) | (~spl4_1 | ~spl4_5 | ~spl4_7)),
% 0.22/0.54    inference(superposition,[],[f308,f103])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | ~spl4_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f102])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    spl4_5 <=> k1_xboole_0 = sK0),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.54  fof(f308,plain,(
% 0.22/0.54    ( ! [X12] : (r1_tarski(k7_relat_1(sK3,X12),k2_zfmisc_1(sK0,sK1))) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(forward_demodulation,[],[f290,f127])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    ( ! [X2] : (k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(subsumption_resolution,[],[f116,f85])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    v1_funct_1(sK3) | ~spl4_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    spl4_1 <=> v1_funct_1(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    ( ! [X2] : (~v1_funct_1(sK3) | k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)) ) | ~spl4_7),
% 0.22/0.54    inference(resolution,[],[f110,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f109])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.54  fof(f290,plain,(
% 0.22/0.54    ( ! [X12] : (r1_tarski(k2_partfun1(sK0,sK1,sK3,X12),k2_zfmisc_1(sK0,sK1))) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(resolution,[],[f126,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(subsumption_resolution,[],[f115,f85])).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    ( ! [X1] : (~v1_funct_1(sK3) | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl4_7),
% 0.22/0.54    inference(resolution,[],[f110,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.22/0.54  fof(f1162,plain,(
% 0.22/0.54    ~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) | spl4_60),
% 0.22/0.54    inference(avatar_component_clause,[],[f1161])).
% 0.22/0.54  fof(f1161,plain,(
% 0.22/0.54    spl4_60 <=> v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 0.22/0.54  fof(f1163,plain,(
% 0.22/0.54    ~spl4_60 | spl4_42 | ~spl4_47),
% 0.22/0.54    inference(avatar_split_clause,[],[f889,f805,f768,f1161])).
% 0.22/0.54  fof(f768,plain,(
% 0.22/0.54    spl4_42 <=> v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.22/0.54  fof(f889,plain,(
% 0.22/0.54    ~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_42 | ~spl4_47)),
% 0.22/0.54    inference(superposition,[],[f769,f806])).
% 0.22/0.54  fof(f769,plain,(
% 0.22/0.54    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | spl4_42),
% 0.22/0.54    inference(avatar_component_clause,[],[f768])).
% 0.22/0.54  fof(f1007,plain,(
% 0.22/0.54    spl4_54 | ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_47),
% 0.22/0.54    inference(avatar_split_clause,[],[f895,f805,f105,f102,f94,f1005])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    spl4_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    spl4_6 <=> k1_xboole_0 = sK1),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.54  fof(f895,plain,(
% 0.22/0.54    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_47)),
% 0.22/0.54    inference(forward_demodulation,[],[f894,f103])).
% 0.22/0.54  fof(f894,plain,(
% 0.22/0.54    v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (~spl4_3 | ~spl4_6 | ~spl4_47)),
% 0.22/0.54    inference(forward_demodulation,[],[f832,f159])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | ~spl4_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f105])).
% 0.22/0.54  fof(f832,plain,(
% 0.22/0.54    v1_funct_2(k1_xboole_0,sK0,sK1) | (~spl4_3 | ~spl4_47)),
% 0.22/0.54    inference(superposition,[],[f95,f806])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    v1_funct_2(sK3,sK0,sK1) | ~spl4_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f94])).
% 0.22/0.54  fof(f807,plain,(
% 0.22/0.54    spl4_47 | ~spl4_44),
% 0.22/0.54    inference(avatar_split_clause,[],[f801,f776,f805])).
% 0.22/0.54  fof(f776,plain,(
% 0.22/0.54    spl4_44 <=> r1_tarski(sK3,k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.22/0.54  fof(f801,plain,(
% 0.22/0.54    k1_xboole_0 = sK3 | ~spl4_44),
% 0.22/0.54    inference(resolution,[],[f777,f55])).
% 0.22/0.54  fof(f777,plain,(
% 0.22/0.54    r1_tarski(sK3,k1_xboole_0) | ~spl4_44),
% 0.22/0.54    inference(avatar_component_clause,[],[f776])).
% 0.22/0.54  fof(f778,plain,(
% 0.22/0.54    spl4_44 | ~spl4_6 | ~spl4_15),
% 0.22/0.54    inference(avatar_split_clause,[],[f238,f181,f105,f776])).
% 0.22/0.54  fof(f181,plain,(
% 0.22/0.54    spl4_15 <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.54  fof(f238,plain,(
% 0.22/0.54    r1_tarski(sK3,k1_xboole_0) | (~spl4_6 | ~spl4_15)),
% 0.22/0.54    inference(forward_demodulation,[],[f233,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f233,plain,(
% 0.22/0.54    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | (~spl4_6 | ~spl4_15)),
% 0.22/0.54    inference(superposition,[],[f182,f159])).
% 0.22/0.54  fof(f182,plain,(
% 0.22/0.54    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl4_15),
% 0.22/0.54    inference(avatar_component_clause,[],[f181])).
% 0.22/0.54  fof(f770,plain,(
% 0.22/0.54    ~spl4_42 | ~spl4_6 | ~spl4_25 | spl4_36),
% 0.22/0.54    inference(avatar_split_clause,[],[f763,f509,f263,f105,f768])).
% 0.22/0.54  fof(f263,plain,(
% 0.22/0.54    spl4_25 <=> k1_xboole_0 = sK2),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.54  fof(f509,plain,(
% 0.22/0.54    spl4_36 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.22/0.54  fof(f763,plain,(
% 0.22/0.54    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (~spl4_6 | ~spl4_25 | spl4_36)),
% 0.22/0.54    inference(forward_demodulation,[],[f762,f264])).
% 0.22/0.54  fof(f264,plain,(
% 0.22/0.54    k1_xboole_0 = sK2 | ~spl4_25),
% 0.22/0.54    inference(avatar_component_clause,[],[f263])).
% 0.22/0.54  fof(f762,plain,(
% 0.22/0.54    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) | (~spl4_6 | spl4_36)),
% 0.22/0.54    inference(forward_demodulation,[],[f760,f159])).
% 0.22/0.54  fof(f760,plain,(
% 0.22/0.54    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_36),
% 0.22/0.54    inference(avatar_component_clause,[],[f509])).
% 0.22/0.54  fof(f761,plain,(
% 0.22/0.54    ~spl4_36 | ~spl4_1 | ~spl4_7 | spl4_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f618,f139,f109,f84,f509])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    spl4_10 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.54  fof(f618,plain,(
% 0.22/0.54    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (~spl4_1 | ~spl4_7 | spl4_10)),
% 0.22/0.54    inference(forward_demodulation,[],[f140,f127])).
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f139])).
% 0.22/0.54  fof(f617,plain,(
% 0.22/0.54    ~spl4_1 | ~spl4_7 | spl4_11 | ~spl4_30),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f616])).
% 0.22/0.54  fof(f616,plain,(
% 0.22/0.54    $false | (~spl4_1 | ~spl4_7 | spl4_11 | ~spl4_30)),
% 0.22/0.54    inference(subsumption_resolution,[],[f610,f147])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_11),
% 0.22/0.54    inference(avatar_component_clause,[],[f146])).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    spl4_11 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.54  fof(f610,plain,(
% 0.22/0.54    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_1 | ~spl4_7 | ~spl4_30)),
% 0.22/0.54    inference(superposition,[],[f342,f357])).
% 0.22/0.54  fof(f357,plain,(
% 0.22/0.54    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_30),
% 0.22/0.54    inference(avatar_component_clause,[],[f356])).
% 0.22/0.54  fof(f356,plain,(
% 0.22/0.54    spl4_30 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.22/0.54  fof(f342,plain,(
% 0.22/0.54    ( ! [X2] : (m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(subsumption_resolution,[],[f341,f304])).
% 0.22/0.54  fof(f304,plain,(
% 0.22/0.54    ( ! [X8] : (v1_relat_1(k7_relat_1(sK3,X8))) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(forward_demodulation,[],[f286,f127])).
% 0.22/0.54  fof(f286,plain,(
% 0.22/0.54    ( ! [X8] : (v1_relat_1(k2_partfun1(sK0,sK1,sK3,X8))) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(resolution,[],[f126,f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.54  fof(f341,plain,(
% 0.22/0.54    ( ! [X2] : (~v1_relat_1(k7_relat_1(sK3,X2)) | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(subsumption_resolution,[],[f336,f280])).
% 0.22/0.54  fof(f280,plain,(
% 0.22/0.54    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(superposition,[],[f124,f127])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(subsumption_resolution,[],[f114,f85])).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_funct_1(sK3) | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) ) | ~spl4_7),
% 0.22/0.54    inference(resolution,[],[f110,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f336,plain,(
% 0.22/0.54    ( ! [X2] : (~v1_funct_1(k7_relat_1(sK3,X2)) | ~v1_relat_1(k7_relat_1(sK3,X2)) | m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X2)),sK1)))) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(resolution,[],[f312,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.22/0.54  fof(f312,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(subsumption_resolution,[],[f311,f304])).
% 0.22/0.54  fof(f311,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(resolution,[],[f306,f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.54  fof(f306,plain,(
% 0.22/0.54    ( ! [X10] : (v5_relat_1(k7_relat_1(sK3,X10),sK1)) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(forward_demodulation,[],[f288,f127])).
% 0.22/0.54  fof(f288,plain,(
% 0.22/0.54    ( ! [X10] : (v5_relat_1(k2_partfun1(sK0,sK1,sK3,X10),sK1)) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(resolution,[],[f126,f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.54  fof(f511,plain,(
% 0.22/0.54    spl4_36 | ~spl4_1 | ~spl4_7 | ~spl4_30),
% 0.22/0.54    inference(avatar_split_clause,[],[f497,f356,f109,f84,f509])).
% 0.22/0.54  fof(f497,plain,(
% 0.22/0.54    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (~spl4_1 | ~spl4_7 | ~spl4_30)),
% 0.22/0.54    inference(superposition,[],[f340,f357])).
% 0.22/0.54  fof(f340,plain,(
% 0.22/0.54    ( ! [X1] : (v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(subsumption_resolution,[],[f339,f304])).
% 0.22/0.54  fof(f339,plain,(
% 0.22/0.54    ( ! [X1] : (~v1_relat_1(k7_relat_1(sK3,X1)) | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(subsumption_resolution,[],[f335,f280])).
% 0.22/0.54  fof(f335,plain,(
% 0.22/0.54    ( ! [X1] : (~v1_funct_1(k7_relat_1(sK3,X1)) | ~v1_relat_1(k7_relat_1(sK3,X1)) | v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(resolution,[],[f312,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f403,plain,(
% 0.22/0.54    ~spl4_1 | ~spl4_5 | ~spl4_6 | ~spl4_7 | spl4_11 | ~spl4_25),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f402])).
% 0.22/0.54  fof(f402,plain,(
% 0.22/0.54    $false | (~spl4_1 | ~spl4_5 | ~spl4_6 | ~spl4_7 | spl4_11 | ~spl4_25)),
% 0.22/0.54    inference(subsumption_resolution,[],[f372,f401])).
% 0.22/0.54  fof(f401,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0))) ) | (~spl4_1 | ~spl4_5 | ~spl4_7)),
% 0.22/0.54    inference(forward_demodulation,[],[f388,f77])).
% 0.22/0.54  fof(f388,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))) ) | (~spl4_1 | ~spl4_5 | ~spl4_7)),
% 0.22/0.54    inference(superposition,[],[f291,f103])).
% 0.22/0.54  fof(f291,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(superposition,[],[f126,f127])).
% 0.22/0.54  fof(f372,plain,(
% 0.22/0.54    ~m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_6 | spl4_11 | ~spl4_25)),
% 0.22/0.54    inference(forward_demodulation,[],[f171,f264])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) | (~spl4_6 | spl4_11)),
% 0.22/0.54    inference(forward_demodulation,[],[f168,f76])).
% 0.22/0.54  fof(f168,plain,(
% 0.22/0.54    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) | (~spl4_6 | spl4_11)),
% 0.22/0.54    inference(superposition,[],[f147,f159])).
% 0.22/0.54  fof(f358,plain,(
% 0.22/0.54    spl4_30 | ~spl4_2 | ~spl4_8 | ~spl4_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f354,f156,f132,f88,f356])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    spl4_2 <=> r1_tarski(sK2,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    spl4_8 <=> v1_relat_1(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    spl4_13 <=> sK0 = k1_relat_1(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.54  fof(f354,plain,(
% 0.22/0.54    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | (~spl4_2 | ~spl4_8 | ~spl4_13)),
% 0.22/0.54    inference(resolution,[],[f179,f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    r1_tarski(sK2,sK0) | ~spl4_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f88])).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | (~spl4_8 | ~spl4_13)),
% 0.22/0.54    inference(subsumption_resolution,[],[f178,f133])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    v1_relat_1(sK3) | ~spl4_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f132])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | ~v1_relat_1(sK3) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | ~spl4_13),
% 0.22/0.54    inference(superposition,[],[f70,f157])).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    sK0 = k1_relat_1(sK3) | ~spl4_13),
% 0.22/0.54    inference(avatar_component_clause,[],[f156])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.22/0.54  fof(f265,plain,(
% 0.22/0.54    spl4_25 | ~spl4_14),
% 0.22/0.54    inference(avatar_split_clause,[],[f243,f175,f263])).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    spl4_14 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.54  fof(f243,plain,(
% 0.22/0.54    k1_xboole_0 = sK2 | ~spl4_14),
% 0.22/0.54    inference(resolution,[],[f176,f55])).
% 0.22/0.54  fof(f176,plain,(
% 0.22/0.54    r1_tarski(sK2,k1_xboole_0) | ~spl4_14),
% 0.22/0.54    inference(avatar_component_clause,[],[f175])).
% 0.22/0.54  fof(f183,plain,(
% 0.22/0.54    spl4_15 | ~spl4_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f123,f109,f181])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl4_7),
% 0.22/0.54    inference(resolution,[],[f110,f64])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    spl4_14 | ~spl4_2 | ~spl4_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f164,f102,f88,f175])).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    r1_tarski(sK2,k1_xboole_0) | (~spl4_2 | ~spl4_5)),
% 0.22/0.54    inference(superposition,[],[f89,f103])).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    spl4_13 | ~spl4_3 | spl4_6 | ~spl4_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f130,f109,f105,f94,f156])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    sK0 = k1_relat_1(sK3) | (~spl4_3 | spl4_6 | ~spl4_7)),
% 0.22/0.54    inference(forward_demodulation,[],[f120,f129])).
% 0.22/0.54  fof(f129,plain,(
% 0.22/0.54    sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl4_3 | spl4_6 | ~spl4_7)),
% 0.22/0.54    inference(subsumption_resolution,[],[f128,f95])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (spl4_6 | ~spl4_7)),
% 0.22/0.54    inference(subsumption_resolution,[],[f118,f106])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    k1_xboole_0 != sK1 | spl4_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f105])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl4_7),
% 0.22/0.54    inference(resolution,[],[f110,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl4_7),
% 0.22/0.54    inference(resolution,[],[f110,f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.54  fof(f148,plain,(
% 0.22/0.54    ~spl4_11 | ~spl4_1 | ~spl4_7 | spl4_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f142,f136,f109,f84,f146])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    spl4_9 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_1 | ~spl4_7 | spl4_9)),
% 0.22/0.54    inference(forward_demodulation,[],[f137,f127])).
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f136])).
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    ~spl4_9 | ~spl4_10 | ~spl4_1 | ~spl4_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f125,f109,f84,f139,f136])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_1 | ~spl4_7)),
% 0.22/0.54    inference(subsumption_resolution,[],[f43,f124])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.54    inference(ennf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.54    inference(negated_conjecture,[],[f18])).
% 0.22/0.54  fof(f18,conjecture,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    spl4_8 | ~spl4_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f119,f109,f132])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    v1_relat_1(sK3) | ~spl4_7),
% 0.22/0.54    inference(resolution,[],[f110,f66])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    spl4_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f47,f109])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    spl4_5 | ~spl4_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f44,f105,f102])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    spl4_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f46,f94])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    spl4_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f48,f88])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    r1_tarski(sK2,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    spl4_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f45,f84])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    v1_funct_1(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (24178)------------------------------
% 0.22/0.54  % (24178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24178)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (24178)Memory used [KB]: 6780
% 0.22/0.54  % (24178)Time elapsed: 0.116 s
% 0.22/0.54  % (24178)------------------------------
% 0.22/0.54  % (24178)------------------------------
% 0.22/0.54  % (24177)Success in time 0.175 s
%------------------------------------------------------------------------------
