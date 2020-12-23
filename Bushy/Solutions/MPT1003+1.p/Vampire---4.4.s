%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t51_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:47 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 224 expanded)
%              Number of leaves         :   29 (  91 expanded)
%              Depth                    :   11
%              Number of atoms          :  313 ( 650 expanded)
%              Number of equality atoms :  112 ( 245 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f478,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f103,f107,f128,f132,f141,f150,f183,f242,f307,f344,f366,f367,f368,f369,f422,f450,f452,f473])).

fof(f473,plain,
    ( ~ spl4_0
    | spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | spl4_17 ),
    inference(avatar_contradiction_clause,[],[f472])).

fof(f472,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f137,f270])).

fof(f270,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != sK0
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(superposition,[],[f149,f108])).

fof(f108,plain,
    ( ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl4_6 ),
    inference(resolution,[],[f106,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t51_funct_2.p',redefinition_k8_relset_1)).

fof(f106,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f149,plain,
    ( k8_relset_1(sK0,sK1,sK2,k2_relat_1(sK2)) != sK0
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_17
  <=> k8_relset_1(sK0,sK1,sK2,k2_relat_1(sK2)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f137,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = sK0
    | ~ spl4_0
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f135,f124])).

fof(f124,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ spl4_0
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f115,f122])).

fof(f122,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | ~ spl4_0
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f121,f95])).

fof(f95,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_0
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f121,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f113,f102])).

fof(f102,plain,
    ( k1_xboole_0 != sK1
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_5
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f113,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f106,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t51_funct_2.p',d1_funct_2)).

fof(f115,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f106,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t51_funct_2.p',redefinition_k1_relset_1)).

fof(f135,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl4_8 ),
    inference(resolution,[],[f127,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t51_funct_2.p',t169_relat_1)).

fof(f127,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl4_8
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f452,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2))
    | k1_xboole_0 = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(theory_axiom,[])).

fof(f450,plain,
    ( spl4_78
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f135,f126,f448])).

fof(f448,plain,
    ( spl4_78
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f422,plain,
    ( ~ spl4_37
    | ~ spl4_2
    | ~ spl4_6
    | spl4_13
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f276,f258,f139,f105,f98,f420])).

fof(f420,plain,
    ( spl4_37
  <=> k1_xboole_0 != k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f98,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f139,plain,
    ( spl4_13
  <=> k8_relset_1(sK0,sK1,sK2,k9_relat_1(sK2,sK0)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f258,plain,
    ( spl4_42
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f276,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f275,f259])).

fof(f259,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f258])).

fof(f275,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0))
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f271,f99])).

fof(f99,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f271,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) != sK0
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(superposition,[],[f140,f108])).

fof(f140,plain,
    ( k8_relset_1(sK0,sK1,sK2,k9_relat_1(sK2,sK0)) != sK0
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f139])).

fof(f369,plain,
    ( k1_xboole_0 != sK0
    | k1_relset_1(sK0,sK1,sK2) != k1_relat_1(sK2)
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK1,sK2)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(theory_axiom,[])).

fof(f368,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != sK1
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2) ),
    introduced(theory_axiom,[])).

fof(f367,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | k1_relset_1(sK0,sK1,sK2) != k1_relat_1(sK2)
    | k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2))
    | k2_relat_1(sK2) = k9_relat_1(sK2,k1_xboole_0) ),
    introduced(theory_axiom,[])).

fof(f366,plain,
    ( spl4_48
    | ~ spl4_20
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f356,f305,f181,f284])).

fof(f284,plain,
    ( spl4_48
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f181,plain,
    ( spl4_20
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f305,plain,
    ( spl4_52
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f356,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl4_20
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f309,f182])).

fof(f182,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f181])).

fof(f309,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl4_52 ),
    inference(resolution,[],[f306,f88])).

fof(f88,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f306,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f305])).

fof(f344,plain,
    ( spl4_58
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f134,f126,f342])).

fof(f342,plain,
    ( spl4_58
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f134,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_8 ),
    inference(resolution,[],[f127,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t51_funct_2.p',t146_relat_1)).

fof(f307,plain,
    ( spl4_52
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f291,f105,f156,f98,f305])).

fof(f156,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f291,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f164,f99])).

fof(f164,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(superposition,[],[f106,f157])).

fof(f157,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f156])).

fof(f242,plain,
    ( spl4_34
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f115,f105,f240])).

fof(f240,plain,
    ( spl4_34
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f183,plain,
    ( spl4_20
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f163,f156,f98,f94,f181])).

fof(f163,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f161,f157])).

fof(f161,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(superposition,[],[f95,f99])).

fof(f150,plain,
    ( ~ spl4_17
    | ~ spl4_0
    | spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | spl4_13 ),
    inference(avatar_split_clause,[],[f142,f139,f126,f105,f101,f94,f148])).

fof(f142,plain,
    ( k8_relset_1(sK0,sK1,sK2,k2_relat_1(sK2)) != sK0
    | ~ spl4_0
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f140,f136])).

fof(f136,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | ~ spl4_0
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f134,f124])).

fof(f141,plain,
    ( ~ spl4_13
    | ~ spl4_6
    | spl4_11 ),
    inference(avatar_split_clause,[],[f133,f130,f105,f139])).

fof(f130,plain,
    ( spl4_11
  <=> k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f133,plain,
    ( k8_relset_1(sK0,sK1,sK2,k9_relat_1(sK2,sK0)) != sK0
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f131,f110])).

fof(f110,plain,
    ( ! [X2] : k7_relset_1(sK0,sK1,sK2,X2) = k9_relat_1(sK2,X2)
    | ~ spl4_6 ),
    inference(resolution,[],[f106,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t51_funct_2.p',redefinition_k7_relset_1)).

fof(f131,plain,
    ( k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) != sK0
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,(
    ~ spl4_11 ),
    inference(avatar_split_clause,[],[f62,f130])).

fof(f62,plain,(
    k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t51_funct_2.p',t51_funct_2)).

fof(f128,plain,
    ( spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f117,f105,f126])).

fof(f117,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f106,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t51_funct_2.p',cc1_relset_1)).

fof(f107,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f61,f105])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f103,plain,
    ( spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f59,f101,f98])).

fof(f59,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f36])).

fof(f96,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f60,f94])).

fof(f60,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
