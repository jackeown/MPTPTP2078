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
% DateTime   : Thu Dec  3 13:17:37 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  214 ( 525 expanded)
%              Number of leaves         :   50 ( 242 expanded)
%              Depth                    :   14
%              Number of atoms          : 1206 (2765 expanded)
%              Number of equality atoms :  124 ( 377 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1841,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f119,f124,f129,f134,f139,f144,f149,f154,f159,f164,f169,f174,f187,f202,f215,f220,f225,f254,f262,f372,f376,f446,f493,f525,f779,f847,f873,f913,f918,f1085,f1220,f1294,f1668,f1676,f1840])).

fof(f1840,plain,
    ( ~ spl8_122
    | ~ spl8_6
    | spl8_16
    | ~ spl8_26
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_123 ),
    inference(avatar_split_clause,[],[f1839,f915,f374,f370,f259,f184,f136,f910])).

fof(f910,plain,
    ( spl8_122
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_122])])).

fof(f136,plain,
    ( spl8_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f184,plain,
    ( spl8_16
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f259,plain,
    ( spl8_26
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f370,plain,
    ( spl8_39
  <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f374,plain,
    ( spl8_40
  <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f915,plain,
    ( spl8_123
  <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_123])])).

fof(f1839,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ spl8_6
    | spl8_16
    | ~ spl8_26
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_123 ),
    inference(forward_demodulation,[],[f1838,f917])).

fof(f917,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl8_123 ),
    inference(avatar_component_clause,[],[f915])).

fof(f1838,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ spl8_6
    | spl8_16
    | ~ spl8_26
    | ~ spl8_39
    | ~ spl8_40 ),
    inference(forward_demodulation,[],[f1837,f371])).

fof(f371,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f370])).

fof(f1837,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl8_6
    | spl8_16
    | ~ spl8_26
    | ~ spl8_40 ),
    inference(forward_demodulation,[],[f1836,f261])).

fof(f261,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f259])).

fof(f1836,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl8_6
    | spl8_16
    | ~ spl8_40 ),
    inference(forward_demodulation,[],[f1835,f347])).

fof(f347,plain,
    ( ! [X5] : k9_subset_1(sK0,X5,sK3) = k1_setfam_1(k2_tarski(X5,sK3))
    | ~ spl8_6 ),
    inference(resolution,[],[f103,f138])).

fof(f138,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f91,f78])).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f1835,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl8_16
    | ~ spl8_40 ),
    inference(forward_demodulation,[],[f186,f375])).

fof(f375,plain,
    ( ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f374])).

fof(f186,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl8_16 ),
    inference(avatar_component_clause,[],[f184])).

fof(f1676,plain,
    ( spl8_14
    | spl8_1
    | ~ spl8_166
    | ~ spl8_143
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_6
    | spl8_7
    | ~ spl8_3
    | spl8_4
    | spl8_2
    | ~ spl8_6
    | ~ spl8_26
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_122
    | ~ spl8_123
    | ~ spl8_176 ),
    inference(avatar_split_clause,[],[f1675,f1291,f915,f910,f374,f370,f259,f136,f116,f126,f121,f141,f136,f156,f151,f146,f171,f166,f161,f1082,f1217,f111,f176])).

fof(f176,plain,
    ( spl8_14
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f111,plain,
    ( spl8_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1217,plain,
    ( spl8_166
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_166])])).

fof(f1082,plain,
    ( spl8_143
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_143])])).

fof(f161,plain,
    ( spl8_11
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f166,plain,
    ( spl8_12
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f171,plain,
    ( spl8_13
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f146,plain,
    ( spl8_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f151,plain,
    ( spl8_9
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f156,plain,
    ( spl8_10
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f141,plain,
    ( spl8_7
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f121,plain,
    ( spl8_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f126,plain,
    ( spl8_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f116,plain,
    ( spl8_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1291,plain,
    ( spl8_176
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_176])])).

fof(f1675,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl8_6
    | ~ spl8_26
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_122
    | ~ spl8_123
    | ~ spl8_176 ),
    inference(trivial_inequality_removal,[],[f1674])).

fof(f1674,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl8_6
    | ~ spl8_26
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_122
    | ~ spl8_123
    | ~ spl8_176 ),
    inference(forward_demodulation,[],[f1673,f912])).

fof(f912,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl8_122 ),
    inference(avatar_component_clause,[],[f910])).

fof(f1673,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl8_6
    | ~ spl8_26
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_123
    | ~ spl8_176 ),
    inference(forward_demodulation,[],[f1672,f917])).

fof(f1672,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl8_6
    | ~ spl8_26
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_176 ),
    inference(forward_demodulation,[],[f1671,f371])).

fof(f1671,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl8_6
    | ~ spl8_26
    | ~ spl8_40
    | ~ spl8_176 ),
    inference(forward_demodulation,[],[f1670,f261])).

fof(f1670,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl8_6
    | ~ spl8_40
    | ~ spl8_176 ),
    inference(forward_demodulation,[],[f1669,f347])).

fof(f1669,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl8_40
    | ~ spl8_176 ),
    inference(forward_demodulation,[],[f1638,f375])).

fof(f1638,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl8_176 ),
    inference(resolution,[],[f1293,f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | v1_xboole_0(X0)
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                        & v1_funct_2(X4,X2,X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                            & v1_funct_2(X5,X3,X1)
                            & v1_funct_1(X5) )
                         => ( k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                                  & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                                  & v1_funct_1(X6) )
                               => ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).

fof(f1293,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl8_176 ),
    inference(avatar_component_clause,[],[f1291])).

fof(f1668,plain,
    ( spl8_15
    | spl8_1
    | ~ spl8_166
    | ~ spl8_143
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_6
    | spl8_7
    | ~ spl8_3
    | spl8_4
    | spl8_2
    | ~ spl8_6
    | ~ spl8_26
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_122
    | ~ spl8_123
    | ~ spl8_176 ),
    inference(avatar_split_clause,[],[f1667,f1291,f915,f910,f374,f370,f259,f136,f116,f126,f121,f141,f136,f156,f151,f146,f171,f166,f161,f1082,f1217,f111,f180])).

fof(f180,plain,
    ( spl8_15
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f1667,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl8_6
    | ~ spl8_26
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_122
    | ~ spl8_123
    | ~ spl8_176 ),
    inference(trivial_inequality_removal,[],[f1666])).

fof(f1666,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl8_6
    | ~ spl8_26
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_122
    | ~ spl8_123
    | ~ spl8_176 ),
    inference(forward_demodulation,[],[f1665,f912])).

fof(f1665,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl8_6
    | ~ spl8_26
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_123
    | ~ spl8_176 ),
    inference(forward_demodulation,[],[f1664,f917])).

fof(f1664,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl8_6
    | ~ spl8_26
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_176 ),
    inference(forward_demodulation,[],[f1663,f371])).

fof(f1663,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl8_6
    | ~ spl8_26
    | ~ spl8_40
    | ~ spl8_176 ),
    inference(forward_demodulation,[],[f1662,f261])).

fof(f1662,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl8_6
    | ~ spl8_40
    | ~ spl8_176 ),
    inference(forward_demodulation,[],[f1661,f347])).

fof(f1661,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl8_40
    | ~ spl8_176 ),
    inference(forward_demodulation,[],[f1637,f375])).

fof(f1637,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl8_176 ),
    inference(resolution,[],[f1293,f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | v1_xboole_0(X0)
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1294,plain,
    ( spl8_176
    | ~ spl8_10
    | ~ spl8_9
    | ~ spl8_8
    | ~ spl8_119 ),
    inference(avatar_split_clause,[],[f1286,f871,f146,f151,f156,f1291])).

fof(f871,plain,
    ( spl8_119
  <=> ! [X1] :
        ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_119])])).

fof(f1286,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl8_8
    | ~ spl8_119 ),
    inference(resolution,[],[f872,f148])).

fof(f148,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f872,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) )
    | ~ spl8_119 ),
    inference(avatar_component_clause,[],[f871])).

fof(f1220,plain,
    ( spl8_166
    | ~ spl8_10
    | ~ spl8_9
    | ~ spl8_8
    | ~ spl8_115 ),
    inference(avatar_split_clause,[],[f1212,f845,f146,f151,f156,f1217])).

fof(f845,plain,
    ( spl8_115
  <=> ! [X1] :
        ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_115])])).

fof(f1212,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl8_8
    | ~ spl8_115 ),
    inference(resolution,[],[f846,f148])).

fof(f846,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) )
    | ~ spl8_115 ),
    inference(avatar_component_clause,[],[f845])).

fof(f1085,plain,
    ( spl8_143
    | ~ spl8_10
    | ~ spl8_9
    | ~ spl8_8
    | ~ spl8_103 ),
    inference(avatar_split_clause,[],[f1077,f777,f146,f151,f156,f1082])).

fof(f777,plain,
    ( spl8_103
  <=> ! [X1] :
        ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).

fof(f1077,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl8_8
    | ~ spl8_103 ),
    inference(resolution,[],[f778,f148])).

fof(f778,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) )
    | ~ spl8_103 ),
    inference(avatar_component_clause,[],[f777])).

fof(f918,plain,
    ( spl8_123
    | ~ spl8_19
    | ~ spl8_21
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f908,f222,f217,f199,f915])).

fof(f199,plain,
    ( spl8_19
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f217,plain,
    ( spl8_21
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f222,plain,
    ( spl8_22
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f908,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl8_19
    | ~ spl8_21
    | ~ spl8_22 ),
    inference(resolution,[],[f342,f219])).

fof(f219,plain,
    ( v1_relat_1(sK5)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f217])).

fof(f342,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(X3)
        | k1_xboole_0 = k7_relat_1(X3,k1_xboole_0) )
    | ~ spl8_19
    | ~ spl8_22 ),
    inference(resolution,[],[f337,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f337,plain,
    ( ! [X2] : r1_xboole_0(X2,k1_xboole_0)
    | ~ spl8_19
    | ~ spl8_22 ),
    inference(resolution,[],[f334,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f334,plain,
    ( ! [X2] : r1_xboole_0(k1_xboole_0,X2)
    | ~ spl8_19
    | ~ spl8_22 ),
    inference(trivial_inequality_removal,[],[f333])).

fof(f333,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(k1_xboole_0,X2) )
    | ~ spl8_19
    | ~ spl8_22 ),
    inference(forward_demodulation,[],[f332,f294])).

fof(f294,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(global_subsumption,[],[f210,f283])).

fof(f283,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f85,f229])).

fof(f229,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f93,f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f210,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f92,f70])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f332,plain,
    ( ! [X2] :
        ( r1_xboole_0(k1_xboole_0,X2)
        | k1_xboole_0 != k7_relat_1(k1_xboole_0,X2) )
    | ~ spl8_19
    | ~ spl8_22 ),
    inference(forward_demodulation,[],[f331,f201])).

fof(f201,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f199])).

fof(f331,plain,
    ( ! [X2] :
        ( r1_xboole_0(k1_relat_1(k1_xboole_0),X2)
        | k1_xboole_0 != k7_relat_1(k1_xboole_0,X2) )
    | ~ spl8_22 ),
    inference(resolution,[],[f81,f224])).

fof(f224,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f222])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f913,plain,
    ( spl8_122
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f907,f222,f212,f199,f910])).

fof(f212,plain,
    ( spl8_20
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f907,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(resolution,[],[f342,f214])).

fof(f214,plain,
    ( v1_relat_1(sK4)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f212])).

fof(f873,plain,
    ( ~ spl8_6
    | ~ spl8_12
    | spl8_7
    | ~ spl8_13
    | spl8_2
    | spl8_119
    | ~ spl8_11
    | ~ spl8_68 ),
    inference(avatar_split_clause,[],[f862,f523,f161,f871,f116,f171,f141,f166,f136])).

fof(f523,plain,
    ( spl8_68
  <=> ! [X16,X13,X15,X14] :
        ( v1_xboole_0(X13)
        | m1_subset_1(k1_tmap_1(sK0,X13,sK2,X14,X15,X16),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X14),X13)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X13)))
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK2,X13)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,sK2,X13)
        | v1_xboole_0(X14)
        | ~ v1_funct_2(X16,X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f862,plain,
    ( ! [X1] :
        ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | v1_xboole_0(sK3)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) )
    | ~ spl8_11
    | ~ spl8_68 ),
    inference(resolution,[],[f524,f163])).

fof(f163,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f161])).

fof(f524,plain,
    ( ! [X14,X15,X13,X16] :
        ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X13)))
        | m1_subset_1(k1_tmap_1(sK0,X13,sK2,X14,X15,X16),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X14),X13)))
        | v1_xboole_0(X13)
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK2,X13)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,sK2,X13)
        | v1_xboole_0(X14)
        | ~ v1_funct_2(X16,X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(sK0)) )
    | ~ spl8_68 ),
    inference(avatar_component_clause,[],[f523])).

fof(f847,plain,
    ( ~ spl8_6
    | ~ spl8_12
    | spl8_7
    | ~ spl8_13
    | spl8_2
    | spl8_115
    | ~ spl8_11
    | ~ spl8_62 ),
    inference(avatar_split_clause,[],[f836,f491,f161,f845,f116,f171,f141,f166,f136])).

fof(f491,plain,
    ( spl8_62
  <=> ! [X16,X13,X15,X14] :
        ( v1_xboole_0(X13)
        | v1_funct_2(k1_tmap_1(sK0,X13,sK2,X14,X15,X16),k4_subset_1(sK0,sK2,X14),X13)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X13)))
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK2,X13)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,sK2,X13)
        | v1_xboole_0(X14)
        | ~ v1_funct_2(X16,X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f836,plain,
    ( ! [X1] :
        ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | v1_xboole_0(sK3)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) )
    | ~ spl8_11
    | ~ spl8_62 ),
    inference(resolution,[],[f492,f163])).

fof(f492,plain,
    ( ! [X14,X15,X13,X16] :
        ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X13)))
        | v1_funct_2(k1_tmap_1(sK0,X13,sK2,X14,X15,X16),k4_subset_1(sK0,sK2,X14),X13)
        | v1_xboole_0(X13)
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK2,X13)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,sK2,X13)
        | v1_xboole_0(X14)
        | ~ v1_funct_2(X16,X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(sK0)) )
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f491])).

fof(f779,plain,
    ( ~ spl8_6
    | ~ spl8_12
    | spl8_7
    | ~ spl8_13
    | spl8_2
    | spl8_103
    | ~ spl8_11
    | ~ spl8_53 ),
    inference(avatar_split_clause,[],[f768,f444,f161,f777,f116,f171,f141,f166,f136])).

fof(f444,plain,
    ( spl8_53
  <=> ! [X16,X13,X15,X14] :
        ( v1_xboole_0(X13)
        | v1_funct_1(k1_tmap_1(sK0,X13,sK2,X14,X15,X16))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X13)))
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK2,X13)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,sK2,X13)
        | v1_xboole_0(X14)
        | ~ v1_funct_2(X16,X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f768,plain,
    ( ! [X1] :
        ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | v1_xboole_0(sK3)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) )
    | ~ spl8_11
    | ~ spl8_53 ),
    inference(resolution,[],[f445,f163])).

fof(f445,plain,
    ( ! [X14,X15,X13,X16] :
        ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X13)))
        | v1_funct_1(k1_tmap_1(sK0,X13,sK2,X14,X15,X16))
        | v1_xboole_0(X13)
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK2,X13)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,sK2,X13)
        | v1_xboole_0(X14)
        | ~ v1_funct_2(X16,X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(sK0)) )
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f444])).

fof(f525,plain,
    ( spl8_1
    | spl8_4
    | spl8_68
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f510,f121,f523,f126,f111])).

fof(f510,plain,
    ( ! [X14,X15,X13,X16] :
        ( v1_xboole_0(X13)
        | v1_xboole_0(sK2)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,sK2,X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK2,X13)))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,X14,X13)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X13)))
        | m1_subset_1(k1_tmap_1(sK0,X13,sK2,X14,X15,X16),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X14),X13))) )
    | ~ spl8_3 ),
    inference(resolution,[],[f100,f123])).

fof(f123,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | v1_xboole_0(X0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(X5,X3,X1)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(X4,X2,X1)
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(f493,plain,
    ( spl8_1
    | spl8_4
    | spl8_62
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f478,f121,f491,f126,f111])).

fof(f478,plain,
    ( ! [X14,X15,X13,X16] :
        ( v1_xboole_0(X13)
        | v1_xboole_0(sK2)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,sK2,X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK2,X13)))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,X14,X13)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X13)))
        | v1_funct_2(k1_tmap_1(sK0,X13,sK2,X14,X15,X16),k4_subset_1(sK0,sK2,X14),X13) )
    | ~ spl8_3 ),
    inference(resolution,[],[f99,f123])).

fof(f99,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | v1_xboole_0(X0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f446,plain,
    ( spl8_1
    | spl8_4
    | spl8_53
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f415,f121,f444,f126,f111])).

fof(f415,plain,
    ( ! [X14,X15,X13,X16] :
        ( v1_xboole_0(X13)
        | v1_xboole_0(sK2)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,sK2,X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK2,X13)))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,X14,X13)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X13)))
        | v1_funct_1(k1_tmap_1(sK0,X13,sK2,X14,X15,X16)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f98,f123])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | v1_xboole_0(X0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f376,plain,
    ( spl8_40
    | ~ spl8_13
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f367,f161,f171,f374])).

fof(f367,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK5)
        | k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) )
    | ~ spl8_11 ),
    inference(resolution,[],[f97,f163])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f372,plain,
    ( spl8_39
    | ~ spl8_10
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f366,f146,f156,f370])).

fof(f366,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) )
    | ~ spl8_8 ),
    inference(resolution,[],[f97,f148])).

fof(f262,plain,
    ( spl8_26
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f256,f251,f259])).

fof(f251,plain,
    ( spl8_25
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f256,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl8_25 ),
    inference(resolution,[],[f253,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f89,f78])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f253,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f251])).

fof(f254,plain,
    ( spl8_4
    | spl8_25
    | spl8_7
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f249,f131,f141,f251,f126])).

fof(f131,plain,
    ( spl8_5
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f249,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2)
    | ~ spl8_5 ),
    inference(resolution,[],[f84,f133])).

fof(f133,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f225,plain,(
    spl8_22 ),
    inference(avatar_split_clause,[],[f210,f222])).

fof(f220,plain,
    ( spl8_21
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f209,f161,f217])).

fof(f209,plain,
    ( v1_relat_1(sK5)
    | ~ spl8_11 ),
    inference(resolution,[],[f92,f163])).

fof(f215,plain,
    ( spl8_20
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f208,f146,f212])).

fof(f208,plain,
    ( v1_relat_1(sK4)
    | ~ spl8_8 ),
    inference(resolution,[],[f92,f148])).

fof(f202,plain,(
    spl8_19 ),
    inference(avatar_split_clause,[],[f68,f199])).

fof(f68,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f187,plain,
    ( ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f53,f184,f180,f176])).

fof(f53,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                      & ~ v1_xboole_0(X3) )
                   => ( r1_subset_1(X2,X3)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                            & v1_funct_2(X4,X2,X1)
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                                & v1_funct_2(X5,X3,X1)
                                & v1_funct_1(X5) )
                             => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                                & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                                & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ( r1_subset_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                          & v1_funct_2(X4,X2,X1)
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                              & v1_funct_2(X5,X3,X1)
                              & v1_funct_1(X5) )
                           => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                              & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                              & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).

fof(f174,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f54,f171])).

fof(f54,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f169,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f55,f166])).

fof(f55,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f164,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f56,f161])).

fof(f56,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f159,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f57,f156])).

fof(f57,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f154,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f58,f151])).

fof(f58,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f149,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f59,f146])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f144,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f60,f141])).

fof(f60,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f139,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f61,f136])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f134,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f62,f131])).

fof(f62,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f129,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f63,f126])).

fof(f63,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f124,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f64,f121])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f119,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f65,f116])).

fof(f65,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f114,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f66,f111])).

fof(f66,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:22:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (29567)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (29594)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.51  % (29578)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.19/0.52  % (29570)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.19/0.52  % (29583)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.19/0.53  % (29575)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.19/0.53  % (29572)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.53  % (29587)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.54  % (29571)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.54  % (29565)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.54  % (29566)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.55  % (29579)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.31/0.55  % (29590)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.55  % (29568)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.56  % (29582)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.31/0.56  % (29580)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.56  % (29582)Refutation not found, incomplete strategy% (29582)------------------------------
% 1.31/0.56  % (29582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (29582)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (29582)Memory used [KB]: 10746
% 1.31/0.56  % (29582)Time elapsed: 0.136 s
% 1.31/0.56  % (29582)------------------------------
% 1.31/0.56  % (29582)------------------------------
% 1.31/0.56  % (29569)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.56  % (29574)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.31/0.57  % (29593)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.57  % (29588)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.57  % (29573)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.31/0.57  % (29585)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.31/0.57  % (29576)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.31/0.57  % (29581)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.58  % (29577)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.58  % (29586)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.31/0.58  % (29575)Refutation not found, incomplete strategy% (29575)------------------------------
% 1.31/0.58  % (29575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.58  % (29575)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.58  
% 1.31/0.58  % (29575)Memory used [KB]: 11513
% 1.31/0.58  % (29575)Time elapsed: 0.146 s
% 1.31/0.58  % (29575)------------------------------
% 1.31/0.58  % (29575)------------------------------
% 1.31/0.58  % (29592)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.58  % (29591)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.58  % (29584)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.31/0.59  % (29589)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.96/0.63  % (29587)Refutation not found, incomplete strategy% (29587)------------------------------
% 1.96/0.63  % (29587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.63  % (29587)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.63  
% 1.96/0.63  % (29587)Memory used [KB]: 11641
% 1.96/0.63  % (29587)Time elapsed: 0.177 s
% 1.96/0.63  % (29587)------------------------------
% 1.96/0.63  % (29587)------------------------------
% 1.96/0.66  % (29581)Refutation found. Thanks to Tanya!
% 1.96/0.66  % SZS status Theorem for theBenchmark
% 1.96/0.66  % SZS output start Proof for theBenchmark
% 1.96/0.66  fof(f1841,plain,(
% 1.96/0.66    $false),
% 1.96/0.66    inference(avatar_sat_refutation,[],[f114,f119,f124,f129,f134,f139,f144,f149,f154,f159,f164,f169,f174,f187,f202,f215,f220,f225,f254,f262,f372,f376,f446,f493,f525,f779,f847,f873,f913,f918,f1085,f1220,f1294,f1668,f1676,f1840])).
% 1.96/0.66  fof(f1840,plain,(
% 1.96/0.66    ~spl8_122 | ~spl8_6 | spl8_16 | ~spl8_26 | ~spl8_39 | ~spl8_40 | ~spl8_123),
% 1.96/0.66    inference(avatar_split_clause,[],[f1839,f915,f374,f370,f259,f184,f136,f910])).
% 1.96/0.66  fof(f910,plain,(
% 1.96/0.66    spl8_122 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 1.96/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_122])])).
% 1.96/0.66  fof(f136,plain,(
% 1.96/0.66    spl8_6 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.96/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.96/0.68  fof(f184,plain,(
% 1.96/0.68    spl8_16 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.96/0.68  fof(f259,plain,(
% 1.96/0.68    spl8_26 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 1.96/0.68  fof(f370,plain,(
% 1.96/0.68    spl8_39 <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 1.96/0.68  fof(f374,plain,(
% 1.96/0.68    spl8_40 <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 1.96/0.68  fof(f915,plain,(
% 1.96/0.68    spl8_123 <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_123])])).
% 1.96/0.68  fof(f1839,plain,(
% 1.96/0.68    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | (~spl8_6 | spl8_16 | ~spl8_26 | ~spl8_39 | ~spl8_40 | ~spl8_123)),
% 1.96/0.68    inference(forward_demodulation,[],[f1838,f917])).
% 1.96/0.68  fof(f917,plain,(
% 1.96/0.68    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | ~spl8_123),
% 1.96/0.68    inference(avatar_component_clause,[],[f915])).
% 1.96/0.68  fof(f1838,plain,(
% 1.96/0.68    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | (~spl8_6 | spl8_16 | ~spl8_26 | ~spl8_39 | ~spl8_40)),
% 1.96/0.68    inference(forward_demodulation,[],[f1837,f371])).
% 1.96/0.68  fof(f371,plain,(
% 1.96/0.68    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl8_39),
% 1.96/0.68    inference(avatar_component_clause,[],[f370])).
% 1.96/0.68  fof(f1837,plain,(
% 1.96/0.68    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (~spl8_6 | spl8_16 | ~spl8_26 | ~spl8_40)),
% 1.96/0.68    inference(forward_demodulation,[],[f1836,f261])).
% 1.96/0.68  fof(f261,plain,(
% 1.96/0.68    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl8_26),
% 1.96/0.68    inference(avatar_component_clause,[],[f259])).
% 1.96/0.68  fof(f1836,plain,(
% 1.96/0.68    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | (~spl8_6 | spl8_16 | ~spl8_40)),
% 1.96/0.68    inference(forward_demodulation,[],[f1835,f347])).
% 1.96/0.68  fof(f347,plain,(
% 1.96/0.68    ( ! [X5] : (k9_subset_1(sK0,X5,sK3) = k1_setfam_1(k2_tarski(X5,sK3))) ) | ~spl8_6),
% 1.96/0.68    inference(resolution,[],[f103,f138])).
% 1.96/0.68  fof(f138,plain,(
% 1.96/0.68    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl8_6),
% 1.96/0.68    inference(avatar_component_clause,[],[f136])).
% 1.96/0.68  fof(f103,plain,(
% 1.96/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 1.96/0.68    inference(definition_unfolding,[],[f91,f78])).
% 1.96/0.68  fof(f78,plain,(
% 1.96/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.96/0.68    inference(cnf_transformation,[],[f7])).
% 1.96/0.68  fof(f7,axiom,(
% 1.96/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.96/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.96/0.68  fof(f91,plain,(
% 1.96/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.96/0.68    inference(cnf_transformation,[],[f42])).
% 1.96/0.68  fof(f42,plain,(
% 1.96/0.68    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.96/0.68    inference(ennf_transformation,[],[f5])).
% 1.96/0.68  fof(f5,axiom,(
% 1.96/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.96/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.96/0.68  fof(f1835,plain,(
% 1.96/0.68    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (spl8_16 | ~spl8_40)),
% 1.96/0.68    inference(forward_demodulation,[],[f186,f375])).
% 1.96/0.68  fof(f375,plain,(
% 1.96/0.68    ( ! [X1] : (k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl8_40),
% 1.96/0.68    inference(avatar_component_clause,[],[f374])).
% 1.96/0.68  fof(f186,plain,(
% 1.96/0.68    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl8_16),
% 1.96/0.68    inference(avatar_component_clause,[],[f184])).
% 1.96/0.68  fof(f1676,plain,(
% 1.96/0.68    spl8_14 | spl8_1 | ~spl8_166 | ~spl8_143 | ~spl8_11 | ~spl8_12 | ~spl8_13 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_6 | spl8_7 | ~spl8_3 | spl8_4 | spl8_2 | ~spl8_6 | ~spl8_26 | ~spl8_39 | ~spl8_40 | ~spl8_122 | ~spl8_123 | ~spl8_176),
% 1.96/0.68    inference(avatar_split_clause,[],[f1675,f1291,f915,f910,f374,f370,f259,f136,f116,f126,f121,f141,f136,f156,f151,f146,f171,f166,f161,f1082,f1217,f111,f176])).
% 1.96/0.68  fof(f176,plain,(
% 1.96/0.68    spl8_14 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.96/0.68  fof(f111,plain,(
% 1.96/0.68    spl8_1 <=> v1_xboole_0(sK0)),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.96/0.68  fof(f1217,plain,(
% 1.96/0.68    spl8_166 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_166])])).
% 1.96/0.68  fof(f1082,plain,(
% 1.96/0.68    spl8_143 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_143])])).
% 1.96/0.68  fof(f161,plain,(
% 1.96/0.68    spl8_11 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.96/0.68  fof(f166,plain,(
% 1.96/0.68    spl8_12 <=> v1_funct_2(sK5,sK3,sK1)),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.96/0.68  fof(f171,plain,(
% 1.96/0.68    spl8_13 <=> v1_funct_1(sK5)),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.96/0.68  fof(f146,plain,(
% 1.96/0.68    spl8_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.96/0.68  fof(f151,plain,(
% 1.96/0.68    spl8_9 <=> v1_funct_2(sK4,sK2,sK1)),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.96/0.68  fof(f156,plain,(
% 1.96/0.68    spl8_10 <=> v1_funct_1(sK4)),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.96/0.68  fof(f141,plain,(
% 1.96/0.68    spl8_7 <=> v1_xboole_0(sK3)),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.96/0.68  fof(f121,plain,(
% 1.96/0.68    spl8_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.96/0.68  fof(f126,plain,(
% 1.96/0.68    spl8_4 <=> v1_xboole_0(sK2)),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.96/0.68  fof(f116,plain,(
% 1.96/0.68    spl8_2 <=> v1_xboole_0(sK1)),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.96/0.68  fof(f1291,plain,(
% 1.96/0.68    spl8_176 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_176])])).
% 1.96/0.68  fof(f1675,plain,(
% 1.96/0.68    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl8_6 | ~spl8_26 | ~spl8_39 | ~spl8_40 | ~spl8_122 | ~spl8_123 | ~spl8_176)),
% 1.96/0.68    inference(trivial_inequality_removal,[],[f1674])).
% 1.96/0.68  fof(f1674,plain,(
% 1.96/0.68    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl8_6 | ~spl8_26 | ~spl8_39 | ~spl8_40 | ~spl8_122 | ~spl8_123 | ~spl8_176)),
% 1.96/0.68    inference(forward_demodulation,[],[f1673,f912])).
% 1.96/0.68  fof(f912,plain,(
% 1.96/0.68    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl8_122),
% 1.96/0.68    inference(avatar_component_clause,[],[f910])).
% 1.96/0.68  fof(f1673,plain,(
% 1.96/0.68    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl8_6 | ~spl8_26 | ~spl8_39 | ~spl8_40 | ~spl8_123 | ~spl8_176)),
% 1.96/0.68    inference(forward_demodulation,[],[f1672,f917])).
% 1.96/0.68  fof(f1672,plain,(
% 1.96/0.68    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl8_6 | ~spl8_26 | ~spl8_39 | ~spl8_40 | ~spl8_176)),
% 1.96/0.68    inference(forward_demodulation,[],[f1671,f371])).
% 1.96/0.68  fof(f1671,plain,(
% 1.96/0.68    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl8_6 | ~spl8_26 | ~spl8_40 | ~spl8_176)),
% 1.96/0.68    inference(forward_demodulation,[],[f1670,f261])).
% 1.96/0.68  fof(f1670,plain,(
% 1.96/0.68    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl8_6 | ~spl8_40 | ~spl8_176)),
% 1.96/0.68    inference(forward_demodulation,[],[f1669,f347])).
% 1.96/0.68  fof(f1669,plain,(
% 1.96/0.68    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl8_40 | ~spl8_176)),
% 1.96/0.68    inference(forward_demodulation,[],[f1638,f375])).
% 1.96/0.68  fof(f1638,plain,(
% 1.96/0.68    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~spl8_176),
% 1.96/0.68    inference(resolution,[],[f1293,f106])).
% 1.96/0.68  fof(f106,plain,(
% 1.96/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 1.96/0.68    inference(equality_resolution,[],[f72])).
% 1.96/0.68  fof(f72,plain,(
% 1.96/0.68    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.96/0.68    inference(cnf_transformation,[],[f30])).
% 1.96/0.68  fof(f30,plain,(
% 1.96/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.96/0.68    inference(flattening,[],[f29])).
% 1.96/0.68  fof(f29,plain,(
% 1.96/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.96/0.68    inference(ennf_transformation,[],[f21])).
% 1.96/0.68  fof(f21,axiom,(
% 1.96/0.68    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 1.96/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).
% 1.96/0.68  fof(f1293,plain,(
% 1.96/0.68    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl8_176),
% 1.96/0.68    inference(avatar_component_clause,[],[f1291])).
% 1.96/0.68  fof(f1668,plain,(
% 1.96/0.68    spl8_15 | spl8_1 | ~spl8_166 | ~spl8_143 | ~spl8_11 | ~spl8_12 | ~spl8_13 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_6 | spl8_7 | ~spl8_3 | spl8_4 | spl8_2 | ~spl8_6 | ~spl8_26 | ~spl8_39 | ~spl8_40 | ~spl8_122 | ~spl8_123 | ~spl8_176),
% 1.96/0.68    inference(avatar_split_clause,[],[f1667,f1291,f915,f910,f374,f370,f259,f136,f116,f126,f121,f141,f136,f156,f151,f146,f171,f166,f161,f1082,f1217,f111,f180])).
% 1.96/0.68  fof(f180,plain,(
% 1.96/0.68    spl8_15 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.96/0.68  fof(f1667,plain,(
% 1.96/0.68    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl8_6 | ~spl8_26 | ~spl8_39 | ~spl8_40 | ~spl8_122 | ~spl8_123 | ~spl8_176)),
% 1.96/0.68    inference(trivial_inequality_removal,[],[f1666])).
% 1.96/0.68  fof(f1666,plain,(
% 1.96/0.68    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl8_6 | ~spl8_26 | ~spl8_39 | ~spl8_40 | ~spl8_122 | ~spl8_123 | ~spl8_176)),
% 1.96/0.68    inference(forward_demodulation,[],[f1665,f912])).
% 1.96/0.68  fof(f1665,plain,(
% 1.96/0.68    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl8_6 | ~spl8_26 | ~spl8_39 | ~spl8_40 | ~spl8_123 | ~spl8_176)),
% 1.96/0.68    inference(forward_demodulation,[],[f1664,f917])).
% 1.96/0.68  fof(f1664,plain,(
% 1.96/0.68    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl8_6 | ~spl8_26 | ~spl8_39 | ~spl8_40 | ~spl8_176)),
% 1.96/0.68    inference(forward_demodulation,[],[f1663,f371])).
% 1.96/0.68  fof(f1663,plain,(
% 1.96/0.68    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl8_6 | ~spl8_26 | ~spl8_40 | ~spl8_176)),
% 1.96/0.68    inference(forward_demodulation,[],[f1662,f261])).
% 1.96/0.68  fof(f1662,plain,(
% 1.96/0.68    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl8_6 | ~spl8_40 | ~spl8_176)),
% 1.96/0.68    inference(forward_demodulation,[],[f1661,f347])).
% 1.96/0.68  fof(f1661,plain,(
% 1.96/0.68    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl8_40 | ~spl8_176)),
% 1.96/0.68    inference(forward_demodulation,[],[f1637,f375])).
% 1.96/0.68  fof(f1637,plain,(
% 1.96/0.68    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~spl8_176),
% 1.96/0.68    inference(resolution,[],[f1293,f107])).
% 1.96/0.68  fof(f107,plain,(
% 1.96/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 1.96/0.68    inference(equality_resolution,[],[f71])).
% 1.96/0.68  fof(f71,plain,(
% 1.96/0.68    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.96/0.68    inference(cnf_transformation,[],[f30])).
% 1.96/0.68  fof(f1294,plain,(
% 1.96/0.68    spl8_176 | ~spl8_10 | ~spl8_9 | ~spl8_8 | ~spl8_119),
% 1.96/0.68    inference(avatar_split_clause,[],[f1286,f871,f146,f151,f156,f1291])).
% 1.96/0.68  fof(f871,plain,(
% 1.96/0.68    spl8_119 <=> ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_119])])).
% 1.96/0.68  fof(f1286,plain,(
% 1.96/0.68    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl8_8 | ~spl8_119)),
% 1.96/0.68    inference(resolution,[],[f872,f148])).
% 1.96/0.68  fof(f148,plain,(
% 1.96/0.68    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl8_8),
% 1.96/0.68    inference(avatar_component_clause,[],[f146])).
% 1.96/0.68  fof(f872,plain,(
% 1.96/0.68    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))) ) | ~spl8_119),
% 1.96/0.68    inference(avatar_component_clause,[],[f871])).
% 1.96/0.68  fof(f1220,plain,(
% 1.96/0.68    spl8_166 | ~spl8_10 | ~spl8_9 | ~spl8_8 | ~spl8_115),
% 1.96/0.68    inference(avatar_split_clause,[],[f1212,f845,f146,f151,f156,f1217])).
% 1.96/0.68  fof(f845,plain,(
% 1.96/0.68    spl8_115 <=> ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 1.96/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_115])])).
% 1.96/0.68  fof(f1212,plain,(
% 1.96/0.68    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl8_8 | ~spl8_115)),
% 1.96/0.68    inference(resolution,[],[f846,f148])).
% 1.96/0.68  fof(f846,plain,(
% 1.96/0.68    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)) ) | ~spl8_115),
% 1.96/0.68    inference(avatar_component_clause,[],[f845])).
% 1.96/0.69  fof(f1085,plain,(
% 1.96/0.69    spl8_143 | ~spl8_10 | ~spl8_9 | ~spl8_8 | ~spl8_103),
% 1.96/0.69    inference(avatar_split_clause,[],[f1077,f777,f146,f151,f156,f1082])).
% 1.96/0.69  fof(f777,plain,(
% 1.96/0.69    spl8_103 <=> ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 1.96/0.69    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).
% 1.96/0.69  fof(f1077,plain,(
% 1.96/0.69    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl8_8 | ~spl8_103)),
% 1.96/0.69    inference(resolution,[],[f778,f148])).
% 1.96/0.69  fof(f778,plain,(
% 1.96/0.69    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))) ) | ~spl8_103),
% 1.96/0.69    inference(avatar_component_clause,[],[f777])).
% 1.96/0.69  fof(f918,plain,(
% 1.96/0.69    spl8_123 | ~spl8_19 | ~spl8_21 | ~spl8_22),
% 1.96/0.69    inference(avatar_split_clause,[],[f908,f222,f217,f199,f915])).
% 1.96/0.69  fof(f199,plain,(
% 1.96/0.69    spl8_19 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.96/0.69    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.96/0.69  fof(f217,plain,(
% 1.96/0.69    spl8_21 <=> v1_relat_1(sK5)),
% 1.96/0.69    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.96/0.69  fof(f222,plain,(
% 1.96/0.69    spl8_22 <=> v1_relat_1(k1_xboole_0)),
% 1.96/0.69    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 1.96/0.69  fof(f908,plain,(
% 1.96/0.69    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | (~spl8_19 | ~spl8_21 | ~spl8_22)),
% 1.96/0.69    inference(resolution,[],[f342,f219])).
% 1.96/0.69  fof(f219,plain,(
% 1.96/0.69    v1_relat_1(sK5) | ~spl8_21),
% 1.96/0.69    inference(avatar_component_clause,[],[f217])).
% 1.96/0.69  fof(f342,plain,(
% 1.96/0.69    ( ! [X3] : (~v1_relat_1(X3) | k1_xboole_0 = k7_relat_1(X3,k1_xboole_0)) ) | (~spl8_19 | ~spl8_22)),
% 1.96/0.69    inference(resolution,[],[f337,f80])).
% 1.96/0.69  fof(f80,plain,(
% 1.96/0.69    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 1.96/0.69    inference(cnf_transformation,[],[f33])).
% 1.96/0.69  fof(f33,plain,(
% 1.96/0.69    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.96/0.69    inference(ennf_transformation,[],[f13])).
% 1.96/0.69  fof(f13,axiom,(
% 1.96/0.69    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.96/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 1.96/0.69  fof(f337,plain,(
% 1.96/0.69    ( ! [X2] : (r1_xboole_0(X2,k1_xboole_0)) ) | (~spl8_19 | ~spl8_22)),
% 1.96/0.69    inference(resolution,[],[f334,f82])).
% 1.96/0.69  fof(f82,plain,(
% 1.96/0.69    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.96/0.69    inference(cnf_transformation,[],[f34])).
% 1.96/0.69  fof(f34,plain,(
% 1.96/0.69    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.96/0.69    inference(ennf_transformation,[],[f4])).
% 1.96/0.69  fof(f4,axiom,(
% 1.96/0.69    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.96/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.96/0.69  fof(f334,plain,(
% 1.96/0.69    ( ! [X2] : (r1_xboole_0(k1_xboole_0,X2)) ) | (~spl8_19 | ~spl8_22)),
% 1.96/0.69    inference(trivial_inequality_removal,[],[f333])).
% 1.96/0.69  fof(f333,plain,(
% 1.96/0.69    ( ! [X2] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X2)) ) | (~spl8_19 | ~spl8_22)),
% 1.96/0.69    inference(forward_demodulation,[],[f332,f294])).
% 1.96/0.69  fof(f294,plain,(
% 1.96/0.69    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.96/0.69    inference(global_subsumption,[],[f210,f283])).
% 1.96/0.69  fof(f283,plain,(
% 1.96/0.69    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.96/0.69    inference(resolution,[],[f85,f229])).
% 1.96/0.69  fof(f229,plain,(
% 1.96/0.69    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 1.96/0.69    inference(resolution,[],[f93,f70])).
% 1.96/0.69  fof(f70,plain,(
% 1.96/0.69    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.96/0.69    inference(cnf_transformation,[],[f6])).
% 1.96/0.69  fof(f6,axiom,(
% 1.96/0.69    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.96/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.96/0.69  fof(f93,plain,(
% 1.96/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.96/0.69    inference(cnf_transformation,[],[f44])).
% 1.96/0.69  fof(f44,plain,(
% 1.96/0.69    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/0.69    inference(ennf_transformation,[],[f26])).
% 1.96/0.69  fof(f26,plain,(
% 1.96/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.96/0.69    inference(pure_predicate_removal,[],[f16])).
% 1.96/0.69  fof(f16,axiom,(
% 1.96/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.96/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.96/0.69  fof(f85,plain,(
% 1.96/0.69    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 1.96/0.69    inference(cnf_transformation,[],[f38])).
% 1.96/0.69  fof(f38,plain,(
% 1.96/0.69    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.96/0.69    inference(flattening,[],[f37])).
% 1.96/0.69  fof(f37,plain,(
% 1.96/0.69    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.96/0.69    inference(ennf_transformation,[],[f10])).
% 1.96/0.69  fof(f10,axiom,(
% 1.96/0.69    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.96/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.96/0.69  fof(f210,plain,(
% 1.96/0.69    v1_relat_1(k1_xboole_0)),
% 1.96/0.69    inference(resolution,[],[f92,f70])).
% 1.96/0.69  fof(f92,plain,(
% 1.96/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.96/0.69    inference(cnf_transformation,[],[f43])).
% 1.96/0.69  fof(f43,plain,(
% 1.96/0.69    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/0.69    inference(ennf_transformation,[],[f15])).
% 1.96/0.69  fof(f15,axiom,(
% 1.96/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.96/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.96/0.69  fof(f332,plain,(
% 1.96/0.69    ( ! [X2] : (r1_xboole_0(k1_xboole_0,X2) | k1_xboole_0 != k7_relat_1(k1_xboole_0,X2)) ) | (~spl8_19 | ~spl8_22)),
% 1.96/0.69    inference(forward_demodulation,[],[f331,f201])).
% 1.96/0.69  fof(f201,plain,(
% 1.96/0.69    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl8_19),
% 1.96/0.69    inference(avatar_component_clause,[],[f199])).
% 1.96/0.69  fof(f331,plain,(
% 1.96/0.69    ( ! [X2] : (r1_xboole_0(k1_relat_1(k1_xboole_0),X2) | k1_xboole_0 != k7_relat_1(k1_xboole_0,X2)) ) | ~spl8_22),
% 1.96/0.69    inference(resolution,[],[f81,f224])).
% 1.96/0.69  fof(f224,plain,(
% 1.96/0.69    v1_relat_1(k1_xboole_0) | ~spl8_22),
% 1.96/0.69    inference(avatar_component_clause,[],[f222])).
% 1.96/0.69  fof(f81,plain,(
% 1.96/0.69    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) )),
% 1.96/0.69    inference(cnf_transformation,[],[f33])).
% 1.96/0.69  fof(f913,plain,(
% 1.96/0.69    spl8_122 | ~spl8_19 | ~spl8_20 | ~spl8_22),
% 1.96/0.69    inference(avatar_split_clause,[],[f907,f222,f212,f199,f910])).
% 1.96/0.69  fof(f212,plain,(
% 1.96/0.69    spl8_20 <=> v1_relat_1(sK4)),
% 1.96/0.69    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.96/0.69  fof(f907,plain,(
% 1.96/0.69    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | (~spl8_19 | ~spl8_20 | ~spl8_22)),
% 1.96/0.69    inference(resolution,[],[f342,f214])).
% 1.96/0.69  fof(f214,plain,(
% 1.96/0.69    v1_relat_1(sK4) | ~spl8_20),
% 1.96/0.69    inference(avatar_component_clause,[],[f212])).
% 1.96/0.69  fof(f873,plain,(
% 1.96/0.69    ~spl8_6 | ~spl8_12 | spl8_7 | ~spl8_13 | spl8_2 | spl8_119 | ~spl8_11 | ~spl8_68),
% 1.96/0.69    inference(avatar_split_clause,[],[f862,f523,f161,f871,f116,f171,f141,f166,f136])).
% 1.96/0.69  fof(f523,plain,(
% 1.96/0.69    spl8_68 <=> ! [X16,X13,X15,X14] : (v1_xboole_0(X13) | m1_subset_1(k1_tmap_1(sK0,X13,sK2,X14,X15,X16),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X14),X13))) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X13))) | ~v1_funct_1(X16) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK2,X13))) | ~v1_funct_1(X15) | ~v1_funct_2(X15,sK2,X13) | v1_xboole_0(X14) | ~v1_funct_2(X16,X14,X13) | ~m1_subset_1(X14,k1_zfmisc_1(sK0)))),
% 1.96/0.69    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).
% 1.96/0.69  fof(f862,plain,(
% 1.96/0.69    ( ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl8_11 | ~spl8_68)),
% 1.96/0.69    inference(resolution,[],[f524,f163])).
% 1.96/0.69  fof(f163,plain,(
% 1.96/0.69    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl8_11),
% 1.96/0.69    inference(avatar_component_clause,[],[f161])).
% 1.96/0.69  fof(f524,plain,(
% 1.96/0.69    ( ! [X14,X15,X13,X16] : (~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X13))) | m1_subset_1(k1_tmap_1(sK0,X13,sK2,X14,X15,X16),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X14),X13))) | v1_xboole_0(X13) | ~v1_funct_1(X16) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK2,X13))) | ~v1_funct_1(X15) | ~v1_funct_2(X15,sK2,X13) | v1_xboole_0(X14) | ~v1_funct_2(X16,X14,X13) | ~m1_subset_1(X14,k1_zfmisc_1(sK0))) ) | ~spl8_68),
% 1.96/0.69    inference(avatar_component_clause,[],[f523])).
% 1.96/0.69  fof(f847,plain,(
% 1.96/0.69    ~spl8_6 | ~spl8_12 | spl8_7 | ~spl8_13 | spl8_2 | spl8_115 | ~spl8_11 | ~spl8_62),
% 1.96/0.69    inference(avatar_split_clause,[],[f836,f491,f161,f845,f116,f171,f141,f166,f136])).
% 1.96/0.69  fof(f491,plain,(
% 1.96/0.69    spl8_62 <=> ! [X16,X13,X15,X14] : (v1_xboole_0(X13) | v1_funct_2(k1_tmap_1(sK0,X13,sK2,X14,X15,X16),k4_subset_1(sK0,sK2,X14),X13) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X13))) | ~v1_funct_1(X16) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK2,X13))) | ~v1_funct_1(X15) | ~v1_funct_2(X15,sK2,X13) | v1_xboole_0(X14) | ~v1_funct_2(X16,X14,X13) | ~m1_subset_1(X14,k1_zfmisc_1(sK0)))),
% 1.96/0.69    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).
% 1.96/0.69  fof(f836,plain,(
% 1.96/0.69    ( ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl8_11 | ~spl8_62)),
% 1.96/0.69    inference(resolution,[],[f492,f163])).
% 1.96/0.69  fof(f492,plain,(
% 1.96/0.69    ( ! [X14,X15,X13,X16] : (~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X13))) | v1_funct_2(k1_tmap_1(sK0,X13,sK2,X14,X15,X16),k4_subset_1(sK0,sK2,X14),X13) | v1_xboole_0(X13) | ~v1_funct_1(X16) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK2,X13))) | ~v1_funct_1(X15) | ~v1_funct_2(X15,sK2,X13) | v1_xboole_0(X14) | ~v1_funct_2(X16,X14,X13) | ~m1_subset_1(X14,k1_zfmisc_1(sK0))) ) | ~spl8_62),
% 1.96/0.69    inference(avatar_component_clause,[],[f491])).
% 1.96/0.69  fof(f779,plain,(
% 1.96/0.69    ~spl8_6 | ~spl8_12 | spl8_7 | ~spl8_13 | spl8_2 | spl8_103 | ~spl8_11 | ~spl8_53),
% 1.96/0.69    inference(avatar_split_clause,[],[f768,f444,f161,f777,f116,f171,f141,f166,f136])).
% 1.96/0.69  fof(f444,plain,(
% 1.96/0.69    spl8_53 <=> ! [X16,X13,X15,X14] : (v1_xboole_0(X13) | v1_funct_1(k1_tmap_1(sK0,X13,sK2,X14,X15,X16)) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X13))) | ~v1_funct_1(X16) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK2,X13))) | ~v1_funct_1(X15) | ~v1_funct_2(X15,sK2,X13) | v1_xboole_0(X14) | ~v1_funct_2(X16,X14,X13) | ~m1_subset_1(X14,k1_zfmisc_1(sK0)))),
% 1.96/0.69    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).
% 1.96/0.69  fof(f768,plain,(
% 1.96/0.69    ( ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl8_11 | ~spl8_53)),
% 1.96/0.69    inference(resolution,[],[f445,f163])).
% 1.96/0.69  fof(f445,plain,(
% 1.96/0.69    ( ! [X14,X15,X13,X16] : (~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X13))) | v1_funct_1(k1_tmap_1(sK0,X13,sK2,X14,X15,X16)) | v1_xboole_0(X13) | ~v1_funct_1(X16) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK2,X13))) | ~v1_funct_1(X15) | ~v1_funct_2(X15,sK2,X13) | v1_xboole_0(X14) | ~v1_funct_2(X16,X14,X13) | ~m1_subset_1(X14,k1_zfmisc_1(sK0))) ) | ~spl8_53),
% 1.96/0.69    inference(avatar_component_clause,[],[f444])).
% 1.96/0.69  fof(f525,plain,(
% 1.96/0.69    spl8_1 | spl8_4 | spl8_68 | ~spl8_3),
% 1.96/0.69    inference(avatar_split_clause,[],[f510,f121,f523,f126,f111])).
% 1.96/0.69  fof(f510,plain,(
% 1.96/0.69    ( ! [X14,X15,X13,X16] : (v1_xboole_0(X13) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X14) | ~m1_subset_1(X14,k1_zfmisc_1(sK0)) | ~v1_funct_1(X15) | ~v1_funct_2(X15,sK2,X13) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK2,X13))) | ~v1_funct_1(X16) | ~v1_funct_2(X16,X14,X13) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X13))) | m1_subset_1(k1_tmap_1(sK0,X13,sK2,X14,X15,X16),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X14),X13)))) ) | ~spl8_3),
% 1.96/0.69    inference(resolution,[],[f100,f123])).
% 1.96/0.69  fof(f123,plain,(
% 1.96/0.69    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl8_3),
% 1.96/0.69    inference(avatar_component_clause,[],[f121])).
% 1.96/0.69  fof(f100,plain,(
% 1.96/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 1.96/0.69    inference(cnf_transformation,[],[f52])).
% 1.96/0.69  fof(f52,plain,(
% 1.96/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.96/0.69    inference(flattening,[],[f51])).
% 1.96/0.69  fof(f51,plain,(
% 1.96/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.96/0.69    inference(ennf_transformation,[],[f22])).
% 1.96/0.69  fof(f22,axiom,(
% 1.96/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.96/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 1.96/0.69  fof(f493,plain,(
% 1.96/0.69    spl8_1 | spl8_4 | spl8_62 | ~spl8_3),
% 1.96/0.69    inference(avatar_split_clause,[],[f478,f121,f491,f126,f111])).
% 1.96/0.69  fof(f478,plain,(
% 1.96/0.69    ( ! [X14,X15,X13,X16] : (v1_xboole_0(X13) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X14) | ~m1_subset_1(X14,k1_zfmisc_1(sK0)) | ~v1_funct_1(X15) | ~v1_funct_2(X15,sK2,X13) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK2,X13))) | ~v1_funct_1(X16) | ~v1_funct_2(X16,X14,X13) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X13))) | v1_funct_2(k1_tmap_1(sK0,X13,sK2,X14,X15,X16),k4_subset_1(sK0,sK2,X14),X13)) ) | ~spl8_3),
% 1.96/0.69    inference(resolution,[],[f99,f123])).
% 1.96/0.69  fof(f99,plain,(
% 1.96/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 1.96/0.69    inference(cnf_transformation,[],[f52])).
% 1.96/0.69  fof(f446,plain,(
% 1.96/0.69    spl8_1 | spl8_4 | spl8_53 | ~spl8_3),
% 1.96/0.69    inference(avatar_split_clause,[],[f415,f121,f444,f126,f111])).
% 1.96/0.69  fof(f415,plain,(
% 1.96/0.69    ( ! [X14,X15,X13,X16] : (v1_xboole_0(X13) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X14) | ~m1_subset_1(X14,k1_zfmisc_1(sK0)) | ~v1_funct_1(X15) | ~v1_funct_2(X15,sK2,X13) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(sK2,X13))) | ~v1_funct_1(X16) | ~v1_funct_2(X16,X14,X13) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X13))) | v1_funct_1(k1_tmap_1(sK0,X13,sK2,X14,X15,X16))) ) | ~spl8_3),
% 1.96/0.69    inference(resolution,[],[f98,f123])).
% 1.96/0.69  fof(f98,plain,(
% 1.96/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 1.96/0.69    inference(cnf_transformation,[],[f52])).
% 1.96/0.69  fof(f376,plain,(
% 1.96/0.69    spl8_40 | ~spl8_13 | ~spl8_11),
% 1.96/0.69    inference(avatar_split_clause,[],[f367,f161,f171,f374])).
% 1.96/0.69  fof(f367,plain,(
% 1.96/0.69    ( ! [X1] : (~v1_funct_1(sK5) | k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl8_11),
% 1.96/0.69    inference(resolution,[],[f97,f163])).
% 1.96/0.69  fof(f97,plain,(
% 1.96/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.96/0.69    inference(cnf_transformation,[],[f50])).
% 1.96/0.69  fof(f50,plain,(
% 1.96/0.69    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.96/0.69    inference(flattening,[],[f49])).
% 1.96/0.69  fof(f49,plain,(
% 1.96/0.69    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.96/0.69    inference(ennf_transformation,[],[f19])).
% 1.96/0.69  fof(f19,axiom,(
% 1.96/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.96/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.96/0.69  fof(f372,plain,(
% 1.96/0.69    spl8_39 | ~spl8_10 | ~spl8_8),
% 1.96/0.69    inference(avatar_split_clause,[],[f366,f146,f156,f370])).
% 1.96/0.69  fof(f366,plain,(
% 1.96/0.69    ( ! [X0] : (~v1_funct_1(sK4) | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl8_8),
% 1.96/0.69    inference(resolution,[],[f97,f148])).
% 1.96/0.69  fof(f262,plain,(
% 1.96/0.69    spl8_26 | ~spl8_25),
% 1.96/0.69    inference(avatar_split_clause,[],[f256,f251,f259])).
% 1.96/0.69  fof(f251,plain,(
% 1.96/0.69    spl8_25 <=> r1_xboole_0(sK2,sK3)),
% 1.96/0.69    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 1.96/0.69  fof(f256,plain,(
% 1.96/0.69    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl8_25),
% 1.96/0.69    inference(resolution,[],[f253,f101])).
% 1.96/0.69  fof(f101,plain,(
% 1.96/0.69    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.96/0.69    inference(definition_unfolding,[],[f89,f78])).
% 1.96/0.69  fof(f89,plain,(
% 1.96/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.96/0.69    inference(cnf_transformation,[],[f2])).
% 1.96/0.69  fof(f2,axiom,(
% 1.96/0.69    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.96/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.96/0.69  fof(f253,plain,(
% 1.96/0.69    r1_xboole_0(sK2,sK3) | ~spl8_25),
% 1.96/0.69    inference(avatar_component_clause,[],[f251])).
% 1.96/0.69  fof(f254,plain,(
% 1.96/0.69    spl8_4 | spl8_25 | spl8_7 | ~spl8_5),
% 1.96/0.69    inference(avatar_split_clause,[],[f249,f131,f141,f251,f126])).
% 1.96/0.69  fof(f131,plain,(
% 1.96/0.69    spl8_5 <=> r1_subset_1(sK2,sK3)),
% 1.96/0.69    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.96/0.69  fof(f249,plain,(
% 1.96/0.69    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | ~spl8_5),
% 1.96/0.69    inference(resolution,[],[f84,f133])).
% 1.96/0.69  fof(f133,plain,(
% 1.96/0.69    r1_subset_1(sK2,sK3) | ~spl8_5),
% 1.96/0.69    inference(avatar_component_clause,[],[f131])).
% 1.96/0.69  fof(f84,plain,(
% 1.96/0.69    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 1.96/0.69    inference(cnf_transformation,[],[f36])).
% 1.96/0.69  fof(f36,plain,(
% 1.96/0.69    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.96/0.69    inference(flattening,[],[f35])).
% 1.96/0.69  fof(f35,plain,(
% 1.96/0.69    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.96/0.69    inference(ennf_transformation,[],[f14])).
% 1.96/0.69  fof(f14,axiom,(
% 1.96/0.69    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 1.96/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 1.96/0.69  fof(f225,plain,(
% 1.96/0.69    spl8_22),
% 1.96/0.69    inference(avatar_split_clause,[],[f210,f222])).
% 1.96/0.69  fof(f220,plain,(
% 1.96/0.69    spl8_21 | ~spl8_11),
% 1.96/0.69    inference(avatar_split_clause,[],[f209,f161,f217])).
% 1.96/0.69  fof(f209,plain,(
% 1.96/0.69    v1_relat_1(sK5) | ~spl8_11),
% 1.96/0.69    inference(resolution,[],[f92,f163])).
% 1.96/0.69  fof(f215,plain,(
% 1.96/0.69    spl8_20 | ~spl8_8),
% 1.96/0.69    inference(avatar_split_clause,[],[f208,f146,f212])).
% 1.96/0.69  fof(f208,plain,(
% 1.96/0.69    v1_relat_1(sK4) | ~spl8_8),
% 1.96/0.69    inference(resolution,[],[f92,f148])).
% 1.96/0.69  fof(f202,plain,(
% 1.96/0.69    spl8_19),
% 1.96/0.69    inference(avatar_split_clause,[],[f68,f199])).
% 1.96/0.69  fof(f68,plain,(
% 1.96/0.69    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.96/0.69    inference(cnf_transformation,[],[f11])).
% 1.96/0.69  fof(f11,axiom,(
% 1.96/0.69    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.96/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.96/0.69  fof(f187,plain,(
% 1.96/0.69    ~spl8_14 | ~spl8_15 | ~spl8_16),
% 1.96/0.69    inference(avatar_split_clause,[],[f53,f184,f180,f176])).
% 1.96/0.69  fof(f53,plain,(
% 1.96/0.69    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.96/0.69    inference(cnf_transformation,[],[f28])).
% 1.96/0.69  fof(f28,plain,(
% 1.96/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.96/0.69    inference(flattening,[],[f27])).
% 1.96/0.69  fof(f27,plain,(
% 1.96/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.96/0.69    inference(ennf_transformation,[],[f24])).
% 1.96/0.69  fof(f24,negated_conjecture,(
% 1.96/0.69    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.96/0.69    inference(negated_conjecture,[],[f23])).
% 1.96/0.69  fof(f23,conjecture,(
% 1.96/0.69    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.96/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).
% 1.96/0.69  fof(f174,plain,(
% 1.96/0.69    spl8_13),
% 1.96/0.69    inference(avatar_split_clause,[],[f54,f171])).
% 1.96/0.69  fof(f54,plain,(
% 1.96/0.69    v1_funct_1(sK5)),
% 1.96/0.69    inference(cnf_transformation,[],[f28])).
% 1.96/0.69  fof(f169,plain,(
% 1.96/0.69    spl8_12),
% 1.96/0.69    inference(avatar_split_clause,[],[f55,f166])).
% 1.96/0.69  fof(f55,plain,(
% 1.96/0.69    v1_funct_2(sK5,sK3,sK1)),
% 1.96/0.69    inference(cnf_transformation,[],[f28])).
% 1.96/0.69  fof(f164,plain,(
% 1.96/0.69    spl8_11),
% 1.96/0.69    inference(avatar_split_clause,[],[f56,f161])).
% 1.96/0.69  fof(f56,plain,(
% 1.96/0.69    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.96/0.69    inference(cnf_transformation,[],[f28])).
% 1.96/0.69  fof(f159,plain,(
% 1.96/0.69    spl8_10),
% 1.96/0.69    inference(avatar_split_clause,[],[f57,f156])).
% 1.96/0.69  fof(f57,plain,(
% 1.96/0.69    v1_funct_1(sK4)),
% 1.96/0.69    inference(cnf_transformation,[],[f28])).
% 1.96/0.69  fof(f154,plain,(
% 1.96/0.69    spl8_9),
% 1.96/0.69    inference(avatar_split_clause,[],[f58,f151])).
% 1.96/0.69  fof(f58,plain,(
% 1.96/0.69    v1_funct_2(sK4,sK2,sK1)),
% 1.96/0.69    inference(cnf_transformation,[],[f28])).
% 1.96/0.69  fof(f149,plain,(
% 1.96/0.69    spl8_8),
% 1.96/0.69    inference(avatar_split_clause,[],[f59,f146])).
% 1.96/0.69  fof(f59,plain,(
% 1.96/0.69    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.96/0.69    inference(cnf_transformation,[],[f28])).
% 1.96/0.69  fof(f144,plain,(
% 1.96/0.69    ~spl8_7),
% 1.96/0.69    inference(avatar_split_clause,[],[f60,f141])).
% 1.96/0.69  fof(f60,plain,(
% 1.96/0.69    ~v1_xboole_0(sK3)),
% 1.96/0.69    inference(cnf_transformation,[],[f28])).
% 1.96/0.69  fof(f139,plain,(
% 1.96/0.69    spl8_6),
% 1.96/0.69    inference(avatar_split_clause,[],[f61,f136])).
% 1.96/0.69  fof(f61,plain,(
% 1.96/0.69    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.96/0.69    inference(cnf_transformation,[],[f28])).
% 1.96/0.69  fof(f134,plain,(
% 1.96/0.69    spl8_5),
% 1.96/0.69    inference(avatar_split_clause,[],[f62,f131])).
% 1.96/0.69  fof(f62,plain,(
% 1.96/0.69    r1_subset_1(sK2,sK3)),
% 1.96/0.69    inference(cnf_transformation,[],[f28])).
% 1.96/0.69  fof(f129,plain,(
% 1.96/0.69    ~spl8_4),
% 1.96/0.69    inference(avatar_split_clause,[],[f63,f126])).
% 1.96/0.69  fof(f63,plain,(
% 1.96/0.69    ~v1_xboole_0(sK2)),
% 1.96/0.69    inference(cnf_transformation,[],[f28])).
% 1.96/0.69  fof(f124,plain,(
% 1.96/0.69    spl8_3),
% 1.96/0.69    inference(avatar_split_clause,[],[f64,f121])).
% 1.96/0.69  fof(f64,plain,(
% 1.96/0.69    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.96/0.69    inference(cnf_transformation,[],[f28])).
% 1.96/0.69  fof(f119,plain,(
% 1.96/0.69    ~spl8_2),
% 1.96/0.69    inference(avatar_split_clause,[],[f65,f116])).
% 1.96/0.69  fof(f65,plain,(
% 1.96/0.69    ~v1_xboole_0(sK1)),
% 1.96/0.69    inference(cnf_transformation,[],[f28])).
% 1.96/0.69  fof(f114,plain,(
% 1.96/0.69    ~spl8_1),
% 1.96/0.69    inference(avatar_split_clause,[],[f66,f111])).
% 1.96/0.69  fof(f66,plain,(
% 1.96/0.69    ~v1_xboole_0(sK0)),
% 1.96/0.69    inference(cnf_transformation,[],[f28])).
% 1.96/0.69  % SZS output end Proof for theBenchmark
% 1.96/0.69  % (29581)------------------------------
% 1.96/0.69  % (29581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.69  % (29581)Termination reason: Refutation
% 1.96/0.69  
% 1.96/0.69  % (29581)Memory used [KB]: 12281
% 1.96/0.69  % (29581)Time elapsed: 0.239 s
% 1.96/0.69  % (29581)------------------------------
% 1.96/0.69  % (29581)------------------------------
% 1.96/0.69  % (29564)Success in time 0.32 s
%------------------------------------------------------------------------------
