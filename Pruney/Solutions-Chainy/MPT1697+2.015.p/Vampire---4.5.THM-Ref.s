%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:28 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  301 ( 671 expanded)
%              Number of leaves         :   72 ( 328 expanded)
%              Depth                    :   14
%              Number of atoms          : 1474 (3181 expanded)
%              Number of equality atoms :  176 ( 463 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1668,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f118,f123,f128,f133,f138,f143,f148,f153,f158,f163,f168,f173,f186,f191,f196,f225,f230,f291,f296,f312,f319,f400,f405,f411,f417,f423,f427,f449,f465,f485,f497,f523,f531,f539,f546,f572,f678,f771,f791,f850,f859,f917,f952,f972,f984,f992,f1004,f1030,f1042,f1573,f1581,f1667])).

fof(f1667,plain,
    ( ~ spl7_125
    | ~ spl7_6
    | spl7_16
    | ~ spl7_36
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_130 ),
    inference(avatar_split_clause,[],[f1666,f1039,f425,f421,f316,f183,f135,f1001])).

fof(f1001,plain,
    ( spl7_125
  <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_125])])).

fof(f135,plain,
    ( spl7_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f183,plain,
    ( spl7_16
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f316,plain,
    ( spl7_36
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f421,plain,
    ( spl7_44
  <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f425,plain,
    ( spl7_45
  <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f1039,plain,
    ( spl7_130
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).

fof(f1666,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | ~ spl7_6
    | spl7_16
    | ~ spl7_36
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_130 ),
    inference(forward_demodulation,[],[f1665,f1041])).

fof(f1041,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_130 ),
    inference(avatar_component_clause,[],[f1039])).

fof(f1665,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_6
    | spl7_16
    | ~ spl7_36
    | ~ spl7_44
    | ~ spl7_45 ),
    inference(forward_demodulation,[],[f1664,f422])).

fof(f422,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f421])).

fof(f1664,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl7_6
    | spl7_16
    | ~ spl7_36
    | ~ spl7_45 ),
    inference(forward_demodulation,[],[f1663,f318])).

fof(f318,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f316])).

fof(f1663,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl7_6
    | spl7_16
    | ~ spl7_45 ),
    inference(forward_demodulation,[],[f1662,f369])).

fof(f369,plain,
    ( ! [X1] : k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))
    | ~ spl7_6 ),
    inference(resolution,[],[f103,f137])).

fof(f137,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f135])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f94,f81])).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f1662,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl7_16
    | ~ spl7_45 ),
    inference(forward_demodulation,[],[f185,f426])).

fof(f426,plain,
    ( ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f425])).

fof(f185,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f183])).

fof(f1581,plain,
    ( spl7_14
    | spl7_1
    | ~ spl7_115
    | ~ spl7_106
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_6
    | spl7_7
    | ~ spl7_3
    | spl7_4
    | spl7_2
    | ~ spl7_6
    | ~ spl7_36
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_119
    | ~ spl7_125
    | ~ spl7_130 ),
    inference(avatar_split_clause,[],[f1580,f1039,f1001,f949,f425,f421,f316,f135,f115,f125,f120,f140,f135,f155,f150,f145,f170,f165,f160,f847,f914,f110,f175])).

fof(f175,plain,
    ( spl7_14
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f110,plain,
    ( spl7_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f914,plain,
    ( spl7_115
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_115])])).

fof(f847,plain,
    ( spl7_106
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f160,plain,
    ( spl7_11
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f165,plain,
    ( spl7_12
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f170,plain,
    ( spl7_13
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f145,plain,
    ( spl7_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f150,plain,
    ( spl7_9
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f155,plain,
    ( spl7_10
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f140,plain,
    ( spl7_7
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f120,plain,
    ( spl7_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f125,plain,
    ( spl7_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f115,plain,
    ( spl7_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f949,plain,
    ( spl7_119
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_119])])).

fof(f1580,plain,
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
    | ~ spl7_6
    | ~ spl7_36
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_119
    | ~ spl7_125
    | ~ spl7_130 ),
    inference(trivial_inequality_removal,[],[f1579])).

fof(f1579,plain,
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
    | ~ spl7_6
    | ~ spl7_36
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_119
    | ~ spl7_125
    | ~ spl7_130 ),
    inference(forward_demodulation,[],[f1578,f1003])).

fof(f1003,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl7_125 ),
    inference(avatar_component_clause,[],[f1001])).

fof(f1578,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
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
    | ~ spl7_6
    | ~ spl7_36
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_119
    | ~ spl7_130 ),
    inference(forward_demodulation,[],[f1577,f1041])).

fof(f1577,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
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
    | ~ spl7_6
    | ~ spl7_36
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f1576,f422])).

fof(f1576,plain,
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
    | ~ spl7_6
    | ~ spl7_36
    | ~ spl7_45
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f1575,f318])).

fof(f1575,plain,
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
    | ~ spl7_6
    | ~ spl7_45
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f1574,f369])).

fof(f1574,plain,
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
    | ~ spl7_45
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f1549,f426])).

fof(f1549,plain,
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
    | ~ spl7_119 ),
    inference(resolution,[],[f951,f106])).

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

fof(f951,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl7_119 ),
    inference(avatar_component_clause,[],[f949])).

fof(f1573,plain,
    ( spl7_15
    | spl7_1
    | ~ spl7_115
    | ~ spl7_106
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_6
    | spl7_7
    | ~ spl7_3
    | spl7_4
    | spl7_2
    | ~ spl7_6
    | ~ spl7_36
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_119
    | ~ spl7_125
    | ~ spl7_130 ),
    inference(avatar_split_clause,[],[f1572,f1039,f1001,f949,f425,f421,f316,f135,f115,f125,f120,f140,f135,f155,f150,f145,f170,f165,f160,f847,f914,f110,f179])).

fof(f179,plain,
    ( spl7_15
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f1572,plain,
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
    | ~ spl7_6
    | ~ spl7_36
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_119
    | ~ spl7_125
    | ~ spl7_130 ),
    inference(trivial_inequality_removal,[],[f1571])).

fof(f1571,plain,
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
    | ~ spl7_6
    | ~ spl7_36
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_119
    | ~ spl7_125
    | ~ spl7_130 ),
    inference(forward_demodulation,[],[f1570,f1003])).

fof(f1570,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
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
    | ~ spl7_6
    | ~ spl7_36
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_119
    | ~ spl7_130 ),
    inference(forward_demodulation,[],[f1569,f1041])).

fof(f1569,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
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
    | ~ spl7_6
    | ~ spl7_36
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f1568,f422])).

fof(f1568,plain,
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
    | ~ spl7_6
    | ~ spl7_36
    | ~ spl7_45
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f1567,f318])).

fof(f1567,plain,
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
    | ~ spl7_6
    | ~ spl7_45
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f1566,f369])).

fof(f1566,plain,
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
    | ~ spl7_45
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f1548,f426])).

fof(f1548,plain,
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
    | ~ spl7_119 ),
    inference(resolution,[],[f951,f107])).

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

fof(f1042,plain,
    ( spl7_130
    | ~ spl7_48
    | ~ spl7_129 ),
    inference(avatar_split_clause,[],[f1034,f1027,f447,f1039])).

fof(f447,plain,
    ( spl7_48
  <=> ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | k1_xboole_0 = k7_relat_1(sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f1027,plain,
    ( spl7_129
  <=> r1_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_129])])).

fof(f1034,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_48
    | ~ spl7_129 ),
    inference(resolution,[],[f1029,f448])).

fof(f448,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f447])).

fof(f1029,plain,
    ( r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl7_129 ),
    inference(avatar_component_clause,[],[f1027])).

fof(f1030,plain,
    ( spl7_129
    | ~ spl7_23
    | ~ spl7_42
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1025,f969,f408,f222,f1027])).

fof(f222,plain,
    ( spl7_23
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f408,plain,
    ( spl7_42
  <=> sK2 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f969,plain,
    ( spl7_122
  <=> k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_122])])).

fof(f1025,plain,
    ( r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl7_23
    | ~ spl7_42
    | ~ spl7_122 ),
    inference(trivial_inequality_removal,[],[f1024])).

fof(f1024,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl7_23
    | ~ spl7_42
    | ~ spl7_122 ),
    inference(superposition,[],[f429,f971])).

fof(f971,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0)
    | ~ spl7_122 ),
    inference(avatar_component_clause,[],[f969])).

fof(f429,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK4,X0)
        | r1_xboole_0(sK2,X0) )
    | ~ spl7_23
    | ~ spl7_42 ),
    inference(backward_demodulation,[],[f343,f410])).

fof(f410,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f408])).

fof(f343,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK4,X0)
        | r1_xboole_0(k1_relat_1(sK4),X0) )
    | ~ spl7_23 ),
    inference(resolution,[],[f85,f224])).

fof(f224,plain,
    ( v1_relat_1(sK4)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f222])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f1004,plain,
    ( spl7_125
    | ~ spl7_61
    | ~ spl7_124 ),
    inference(avatar_split_clause,[],[f996,f989,f521,f1001])).

fof(f521,plain,
    ( spl7_61
  <=> ! [X0] :
        ( ~ r1_xboole_0(sK3,X0)
        | k1_xboole_0 = k7_relat_1(sK5,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f989,plain,
    ( spl7_124
  <=> r1_xboole_0(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).

fof(f996,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl7_61
    | ~ spl7_124 ),
    inference(resolution,[],[f991,f522])).

fof(f522,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK3,X0)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl7_61 ),
    inference(avatar_component_clause,[],[f521])).

fof(f991,plain,
    ( r1_xboole_0(sK3,k1_xboole_0)
    | ~ spl7_124 ),
    inference(avatar_component_clause,[],[f989])).

fof(f992,plain,
    ( spl7_124
    | ~ spl7_24
    | ~ spl7_43
    | ~ spl7_123 ),
    inference(avatar_split_clause,[],[f987,f979,f414,f227,f989])).

fof(f227,plain,
    ( spl7_24
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f414,plain,
    ( spl7_43
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f979,plain,
    ( spl7_123
  <=> k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_123])])).

fof(f987,plain,
    ( r1_xboole_0(sK3,k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_43
    | ~ spl7_123 ),
    inference(trivial_inequality_removal,[],[f986])).

fof(f986,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK3,k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_43
    | ~ spl7_123 ),
    inference(superposition,[],[f503,f981])).

fof(f981,plain,
    ( k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0)
    | ~ spl7_123 ),
    inference(avatar_component_clause,[],[f979])).

fof(f503,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k9_relat_1(sK5,X1)
        | r1_xboole_0(sK3,X1) )
    | ~ spl7_24
    | ~ spl7_43 ),
    inference(backward_demodulation,[],[f344,f416])).

fof(f416,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f414])).

fof(f344,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k9_relat_1(sK5,X1)
        | r1_xboole_0(k1_relat_1(sK5),X1) )
    | ~ spl7_24 ),
    inference(resolution,[],[f85,f229])).

fof(f229,plain,
    ( v1_relat_1(sK5)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f227])).

fof(f984,plain,
    ( spl7_123
    | ~ spl7_24
    | ~ spl7_68
    | ~ spl7_107 ),
    inference(avatar_split_clause,[],[f983,f856,f569,f227,f979])).

fof(f569,plain,
    ( spl7_68
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f856,plain,
    ( spl7_107
  <=> k1_xboole_0 = k7_relat_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_107])])).

fof(f983,plain,
    ( k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_68
    | ~ spl7_107 ),
    inference(forward_demodulation,[],[f976,f571])).

fof(f571,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_68 ),
    inference(avatar_component_clause,[],[f569])).

fof(f976,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_107 ),
    inference(superposition,[],[f827,f858])).

fof(f858,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl7_107 ),
    inference(avatar_component_clause,[],[f856])).

fof(f827,plain,
    ( ! [X0] : k9_relat_1(k7_relat_1(sK5,X0),k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0)
    | ~ spl7_24 ),
    inference(resolution,[],[f373,f70])).

fof(f70,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f373,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k9_relat_1(k7_relat_1(sK5,X3),X2) = k9_relat_1(sK5,X2) )
    | ~ spl7_24 ),
    inference(resolution,[],[f78,f229])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f972,plain,
    ( spl7_122
    | ~ spl7_23
    | ~ spl7_64
    | ~ spl7_68 ),
    inference(avatar_split_clause,[],[f967,f569,f536,f222,f969])).

fof(f536,plain,
    ( spl7_64
  <=> k1_xboole_0 = k7_relat_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f967,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0)
    | ~ spl7_23
    | ~ spl7_64
    | ~ spl7_68 ),
    inference(forward_demodulation,[],[f965,f571])).

fof(f965,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0)
    | ~ spl7_23
    | ~ spl7_64 ),
    inference(superposition,[],[f822,f538])).

fof(f538,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f536])).

fof(f822,plain,
    ( ! [X0] : k9_relat_1(sK4,k1_xboole_0) = k9_relat_1(k7_relat_1(sK4,X0),k1_xboole_0)
    | ~ spl7_23 ),
    inference(resolution,[],[f372,f70])).

fof(f372,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k9_relat_1(sK4,X0) = k9_relat_1(k7_relat_1(sK4,X1),X0) )
    | ~ spl7_23 ),
    inference(resolution,[],[f78,f224])).

fof(f952,plain,
    ( spl7_119
    | ~ spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_99 ),
    inference(avatar_split_clause,[],[f947,f789,f145,f150,f155,f949])).

fof(f789,plain,
    ( spl7_99
  <=> ! [X1] :
        ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_99])])).

fof(f947,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl7_8
    | ~ spl7_99 ),
    inference(resolution,[],[f790,f147])).

fof(f147,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f145])).

fof(f790,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) )
    | ~ spl7_99 ),
    inference(avatar_component_clause,[],[f789])).

fof(f917,plain,
    ( spl7_115
    | ~ spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_95 ),
    inference(avatar_split_clause,[],[f912,f769,f145,f150,f155,f914])).

fof(f769,plain,
    ( spl7_95
  <=> ! [X1] :
        ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f912,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl7_8
    | ~ spl7_95 ),
    inference(resolution,[],[f770,f147])).

fof(f770,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) )
    | ~ spl7_95 ),
    inference(avatar_component_clause,[],[f769])).

fof(f859,plain,
    ( spl7_107
    | ~ spl7_35
    | ~ spl7_63 ),
    inference(avatar_split_clause,[],[f853,f529,f309,f856])).

fof(f309,plain,
    ( spl7_35
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f529,plain,
    ( spl7_63
  <=> ! [X2] :
        ( ~ r1_xboole_0(X2,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f853,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl7_35
    | ~ spl7_63 ),
    inference(resolution,[],[f530,f311])).

fof(f311,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f309])).

fof(f530,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X2) )
    | ~ spl7_63 ),
    inference(avatar_component_clause,[],[f529])).

fof(f850,plain,
    ( spl7_106
    | ~ spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_79 ),
    inference(avatar_split_clause,[],[f845,f676,f145,f150,f155,f847])).

fof(f676,plain,
    ( spl7_79
  <=> ! [X1] :
        ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).

fof(f845,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl7_8
    | ~ spl7_79 ),
    inference(resolution,[],[f677,f147])).

fof(f677,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) )
    | ~ spl7_79 ),
    inference(avatar_component_clause,[],[f676])).

fof(f791,plain,
    ( ~ spl7_6
    | ~ spl7_12
    | spl7_7
    | ~ spl7_13
    | spl7_2
    | spl7_99
    | ~ spl7_11
    | ~ spl7_57 ),
    inference(avatar_split_clause,[],[f783,f495,f160,f789,f115,f170,f140,f165,f135])).

fof(f495,plain,
    ( spl7_57
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(X0)
        | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK2,X0)
        | v1_xboole_0(X1)
        | ~ v1_funct_2(X3,X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f783,plain,
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
    | ~ spl7_11
    | ~ spl7_57 ),
    inference(resolution,[],[f496,f162])).

fof(f162,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f160])).

fof(f496,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0)))
        | v1_xboole_0(X0)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK2,X0)
        | v1_xboole_0(X1)
        | ~ v1_funct_2(X3,X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) )
    | ~ spl7_57 ),
    inference(avatar_component_clause,[],[f495])).

fof(f771,plain,
    ( ~ spl7_6
    | ~ spl7_12
    | spl7_7
    | ~ spl7_13
    | spl7_2
    | spl7_95
    | ~ spl7_11
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f763,f483,f160,f769,f115,f170,f140,f165,f135])).

fof(f483,plain,
    ( spl7_55
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(X0)
        | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK2,X0)
        | v1_xboole_0(X1)
        | ~ v1_funct_2(X3,X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f763,plain,
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
    | ~ spl7_11
    | ~ spl7_55 ),
    inference(resolution,[],[f484,f162])).

fof(f484,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0)
        | v1_xboole_0(X0)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK2,X0)
        | v1_xboole_0(X1)
        | ~ v1_funct_2(X3,X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) )
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f483])).

fof(f678,plain,
    ( ~ spl7_6
    | ~ spl7_12
    | spl7_7
    | ~ spl7_13
    | spl7_2
    | spl7_79
    | ~ spl7_11
    | ~ spl7_51 ),
    inference(avatar_split_clause,[],[f670,f463,f160,f676,f115,f170,f140,f165,f135])).

fof(f463,plain,
    ( spl7_51
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(X0)
        | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK2,X0)
        | v1_xboole_0(X1)
        | ~ v1_funct_2(X3,X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f670,plain,
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
    | ~ spl7_11
    | ~ spl7_51 ),
    inference(resolution,[],[f464,f162])).

fof(f464,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3))
        | v1_xboole_0(X0)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK2,X0)
        | v1_xboole_0(X1)
        | ~ v1_funct_2(X3,X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) )
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f463])).

fof(f572,plain,
    ( spl7_68
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f567,f326,f193,f188,f569])).

fof(f188,plain,
    ( spl7_17
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f193,plain,
    ( spl7_18
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f326,plain,
    ( spl7_38
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f567,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_38 ),
    inference(forward_demodulation,[],[f566,f190])).

fof(f190,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f188])).

fof(f566,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_18
    | ~ spl7_38 ),
    inference(forward_demodulation,[],[f559,f195])).

fof(f195,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f193])).

fof(f559,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl7_38 ),
    inference(resolution,[],[f327,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f327,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f326])).

fof(f546,plain,
    ( spl7_38
    | ~ spl7_23
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f544,f536,f222,f326])).

fof(f544,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_23
    | ~ spl7_64 ),
    inference(superposition,[],[f231,f538])).

fof(f231,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK4,X0))
    | ~ spl7_23 ),
    inference(resolution,[],[f224,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f539,plain,
    ( spl7_64
    | ~ spl7_35
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f534,f447,f309,f536])).

fof(f534,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl7_35
    | ~ spl7_48 ),
    inference(resolution,[],[f448,f311])).

fof(f531,plain,
    ( ~ spl7_24
    | spl7_63
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f508,f414,f529,f227])).

fof(f508,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK3)
        | ~ v1_relat_1(sK5)
        | k1_xboole_0 = k7_relat_1(sK5,X2) )
    | ~ spl7_43 ),
    inference(superposition,[],[f77,f416])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f523,plain,
    ( ~ spl7_24
    | spl7_61
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f506,f414,f521,f227])).

fof(f506,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK3,X0)
        | ~ v1_relat_1(sK5)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl7_43 ),
    inference(superposition,[],[f86,f416])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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

fof(f497,plain,
    ( spl7_1
    | spl7_4
    | spl7_57
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f490,f120,f495,f125,f110])).

fof(f490,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_xboole_0(X0)
        | v1_xboole_0(sK2)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X1,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) )
    | ~ spl7_3 ),
    inference(resolution,[],[f100,f122])).

fof(f122,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f120])).

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
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

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

fof(f485,plain,
    ( spl7_1
    | spl7_4
    | spl7_55
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f478,f120,f483,f125,f110])).

fof(f478,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_xboole_0(X0)
        | v1_xboole_0(sK2)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X1,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f99,f122])).

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
    inference(cnf_transformation,[],[f53])).

fof(f465,plain,
    ( spl7_1
    | spl7_4
    | spl7_51
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f458,f120,f463,f125,f110])).

fof(f458,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_xboole_0(X0)
        | v1_xboole_0(sK2)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X1,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) )
    | ~ spl7_3 ),
    inference(resolution,[],[f98,f122])).

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
    inference(cnf_transformation,[],[f53])).

fof(f449,plain,
    ( ~ spl7_23
    | spl7_48
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f432,f408,f447,f222])).

fof(f432,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | ~ v1_relat_1(sK4)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl7_42 ),
    inference(superposition,[],[f86,f410])).

fof(f427,plain,
    ( spl7_45
    | ~ spl7_13
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f419,f160,f170,f425])).

fof(f419,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK5)
        | k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) )
    | ~ spl7_11 ),
    inference(resolution,[],[f97,f162])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f423,plain,
    ( spl7_44
    | ~ spl7_10
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f418,f145,f155,f421])).

fof(f418,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) )
    | ~ spl7_8 ),
    inference(resolution,[],[f97,f147])).

fof(f417,plain,
    ( ~ spl7_24
    | spl7_43
    | ~ spl7_34
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f412,f402,f293,f414,f227])).

fof(f293,plain,
    ( spl7_34
  <=> v4_relat_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f402,plain,
    ( spl7_41
  <=> v1_partfun1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f412,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl7_41 ),
    inference(resolution,[],[f404,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f404,plain,
    ( v1_partfun1(sK5,sK3)
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f402])).

fof(f411,plain,
    ( ~ spl7_23
    | spl7_42
    | ~ spl7_33
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f406,f397,f288,f408,f222])).

fof(f288,plain,
    ( spl7_33
  <=> v4_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f397,plain,
    ( spl7_40
  <=> v1_partfun1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f406,plain,
    ( ~ v4_relat_1(sK4,sK2)
    | sK2 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl7_40 ),
    inference(resolution,[],[f399,f91])).

fof(f399,plain,
    ( v1_partfun1(sK4,sK2)
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f397])).

fof(f405,plain,
    ( spl7_41
    | ~ spl7_12
    | ~ spl7_13
    | spl7_2
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f395,f160,f115,f170,f165,f402])).

fof(f395,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | ~ spl7_11 ),
    inference(resolution,[],[f82,f162])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f400,plain,
    ( spl7_40
    | ~ spl7_9
    | ~ spl7_10
    | spl7_2
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f394,f145,f115,f155,f150,f397])).

fof(f394,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f82,f147])).

fof(f319,plain,
    ( spl7_36
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f314,f309,f316])).

fof(f314,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl7_35 ),
    inference(resolution,[],[f311,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f93,f81])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f312,plain,
    ( spl7_4
    | spl7_35
    | spl7_7
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f307,f130,f140,f309,f125])).

fof(f130,plain,
    ( spl7_5
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f307,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2)
    | ~ spl7_5 ),
    inference(resolution,[],[f89,f132])).

fof(f132,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f130])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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

fof(f296,plain,
    ( spl7_34
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f286,f160,f293])).

fof(f286,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl7_11 ),
    inference(resolution,[],[f96,f162])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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

fof(f291,plain,
    ( spl7_33
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f285,f145,f288])).

fof(f285,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f96,f147])).

fof(f230,plain,
    ( spl7_24
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f220,f160,f227])).

fof(f220,plain,
    ( v1_relat_1(sK5)
    | ~ spl7_11 ),
    inference(resolution,[],[f95,f162])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f225,plain,
    ( spl7_23
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f219,f145,f222])).

fof(f219,plain,
    ( v1_relat_1(sK4)
    | ~ spl7_8 ),
    inference(resolution,[],[f95,f147])).

fof(f196,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f68,f193])).

fof(f68,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f191,plain,(
    spl7_17 ),
    inference(avatar_split_clause,[],[f69,f188])).

fof(f69,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f186,plain,
    ( ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f54,f183,f179,f175])).

fof(f54,plain,
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

fof(f173,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f55,f170])).

fof(f55,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f168,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f56,f165])).

fof(f56,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f163,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f57,f160])).

fof(f57,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f158,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f58,f155])).

fof(f58,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f153,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f59,f150])).

fof(f59,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f148,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f60,f145])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f143,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f61,f140])).

fof(f61,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f138,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f62,f135])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f133,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f63,f130])).

fof(f63,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f128,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f64,f125])).

fof(f64,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f123,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f65,f120])).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f118,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f66,f115])).

fof(f66,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f113,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f67,f110])).

fof(f67,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (2737)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (2731)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (2724)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (2717)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (2723)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (2730)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (2742)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (2715)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (2716)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (2721)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.44/0.54  % (2720)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.44/0.54  % (2731)Refutation not found, incomplete strategy% (2731)------------------------------
% 1.44/0.54  % (2731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (2731)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (2731)Memory used [KB]: 10746
% 1.44/0.54  % (2731)Time elapsed: 0.138 s
% 1.44/0.54  % (2731)------------------------------
% 1.44/0.54  % (2731)------------------------------
% 1.44/0.55  % (2714)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.44/0.55  % (2745)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.55  % (2722)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.44/0.55  % (2736)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.44/0.55  % (2725)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.44/0.55  % (2735)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.44/0.55  % (2738)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.44/0.55  % (2729)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.44/0.55  % (2726)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.56  % (2727)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.44/0.56  % (2728)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.44/0.56  % (2740)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.59/0.56  % (2743)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.59/0.56  % (2744)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.59/0.56  % (2739)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.59/0.56  % (2734)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.59/0.57  % (2719)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.59/0.57  % (2741)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.59/0.57  % (2718)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.59/0.59  % (2724)Refutation not found, incomplete strategy% (2724)------------------------------
% 1.59/0.59  % (2724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.60  % (2724)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.60  
% 1.59/0.60  % (2724)Memory used [KB]: 11513
% 1.59/0.60  % (2724)Time elapsed: 0.165 s
% 1.59/0.60  % (2724)------------------------------
% 1.59/0.60  % (2724)------------------------------
% 1.59/0.60  % (2738)Refutation not found, incomplete strategy% (2738)------------------------------
% 1.59/0.60  % (2738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.60  % (2738)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.60  
% 1.59/0.60  % (2738)Memory used [KB]: 11513
% 1.59/0.60  % (2738)Time elapsed: 0.170 s
% 1.59/0.60  % (2738)------------------------------
% 1.59/0.60  % (2738)------------------------------
% 1.59/0.61  % (2730)Refutation found. Thanks to Tanya!
% 1.59/0.61  % SZS status Theorem for theBenchmark
% 1.59/0.61  % SZS output start Proof for theBenchmark
% 1.59/0.61  fof(f1668,plain,(
% 1.59/0.61    $false),
% 1.59/0.61    inference(avatar_sat_refutation,[],[f113,f118,f123,f128,f133,f138,f143,f148,f153,f158,f163,f168,f173,f186,f191,f196,f225,f230,f291,f296,f312,f319,f400,f405,f411,f417,f423,f427,f449,f465,f485,f497,f523,f531,f539,f546,f572,f678,f771,f791,f850,f859,f917,f952,f972,f984,f992,f1004,f1030,f1042,f1573,f1581,f1667])).
% 1.59/0.61  fof(f1667,plain,(
% 1.59/0.61    ~spl7_125 | ~spl7_6 | spl7_16 | ~spl7_36 | ~spl7_44 | ~spl7_45 | ~spl7_130),
% 1.59/0.61    inference(avatar_split_clause,[],[f1666,f1039,f425,f421,f316,f183,f135,f1001])).
% 1.59/0.61  fof(f1001,plain,(
% 1.59/0.61    spl7_125 <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_125])])).
% 1.59/0.61  fof(f135,plain,(
% 1.59/0.61    spl7_6 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.59/0.61  fof(f183,plain,(
% 1.59/0.61    spl7_16 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.59/0.61  fof(f316,plain,(
% 1.59/0.61    spl7_36 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 1.59/0.61  fof(f421,plain,(
% 1.59/0.61    spl7_44 <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 1.59/0.61  fof(f425,plain,(
% 1.59/0.61    spl7_45 <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 1.59/0.61  fof(f1039,plain,(
% 1.59/0.61    spl7_130 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).
% 1.59/0.61  fof(f1666,plain,(
% 1.59/0.61    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | (~spl7_6 | spl7_16 | ~spl7_36 | ~spl7_44 | ~spl7_45 | ~spl7_130)),
% 1.59/0.61    inference(forward_demodulation,[],[f1665,f1041])).
% 1.59/0.61  fof(f1041,plain,(
% 1.59/0.61    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl7_130),
% 1.59/0.61    inference(avatar_component_clause,[],[f1039])).
% 1.59/0.61  fof(f1665,plain,(
% 1.59/0.61    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | (~spl7_6 | spl7_16 | ~spl7_36 | ~spl7_44 | ~spl7_45)),
% 1.59/0.61    inference(forward_demodulation,[],[f1664,f422])).
% 1.59/0.61  fof(f422,plain,(
% 1.59/0.61    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl7_44),
% 1.59/0.61    inference(avatar_component_clause,[],[f421])).
% 1.59/0.61  fof(f1664,plain,(
% 1.59/0.61    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (~spl7_6 | spl7_16 | ~spl7_36 | ~spl7_45)),
% 1.59/0.61    inference(forward_demodulation,[],[f1663,f318])).
% 1.59/0.61  fof(f318,plain,(
% 1.59/0.61    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl7_36),
% 1.59/0.61    inference(avatar_component_clause,[],[f316])).
% 1.59/0.61  fof(f1663,plain,(
% 1.59/0.61    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | (~spl7_6 | spl7_16 | ~spl7_45)),
% 1.59/0.61    inference(forward_demodulation,[],[f1662,f369])).
% 1.59/0.61  fof(f369,plain,(
% 1.59/0.61    ( ! [X1] : (k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))) ) | ~spl7_6),
% 1.59/0.61    inference(resolution,[],[f103,f137])).
% 1.59/0.61  fof(f137,plain,(
% 1.59/0.61    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl7_6),
% 1.59/0.61    inference(avatar_component_clause,[],[f135])).
% 1.59/0.61  fof(f103,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 1.59/0.61    inference(definition_unfolding,[],[f94,f81])).
% 1.59/0.61  fof(f81,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f5])).
% 1.59/0.61  fof(f5,axiom,(
% 1.59/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.59/0.61  fof(f94,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f47])).
% 1.59/0.61  fof(f47,plain,(
% 1.59/0.61    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.59/0.61    inference(ennf_transformation,[],[f3])).
% 1.59/0.61  fof(f3,axiom,(
% 1.59/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.59/0.61  fof(f1662,plain,(
% 1.59/0.61    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (spl7_16 | ~spl7_45)),
% 1.59/0.61    inference(forward_demodulation,[],[f185,f426])).
% 1.59/0.61  fof(f426,plain,(
% 1.59/0.61    ( ! [X1] : (k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl7_45),
% 1.59/0.61    inference(avatar_component_clause,[],[f425])).
% 1.59/0.61  fof(f185,plain,(
% 1.59/0.61    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl7_16),
% 1.59/0.61    inference(avatar_component_clause,[],[f183])).
% 1.59/0.61  fof(f1581,plain,(
% 1.59/0.61    spl7_14 | spl7_1 | ~spl7_115 | ~spl7_106 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_6 | spl7_7 | ~spl7_3 | spl7_4 | spl7_2 | ~spl7_6 | ~spl7_36 | ~spl7_44 | ~spl7_45 | ~spl7_119 | ~spl7_125 | ~spl7_130),
% 1.59/0.61    inference(avatar_split_clause,[],[f1580,f1039,f1001,f949,f425,f421,f316,f135,f115,f125,f120,f140,f135,f155,f150,f145,f170,f165,f160,f847,f914,f110,f175])).
% 1.59/0.61  fof(f175,plain,(
% 1.59/0.61    spl7_14 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.59/0.61  fof(f110,plain,(
% 1.59/0.61    spl7_1 <=> v1_xboole_0(sK0)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.59/0.61  fof(f914,plain,(
% 1.59/0.61    spl7_115 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_115])])).
% 1.59/0.61  fof(f847,plain,(
% 1.59/0.61    spl7_106 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).
% 1.59/0.61  fof(f160,plain,(
% 1.59/0.61    spl7_11 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.59/0.61  fof(f165,plain,(
% 1.59/0.61    spl7_12 <=> v1_funct_2(sK5,sK3,sK1)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.59/0.61  fof(f170,plain,(
% 1.59/0.61    spl7_13 <=> v1_funct_1(sK5)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.59/0.61  fof(f145,plain,(
% 1.59/0.61    spl7_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.59/0.61  fof(f150,plain,(
% 1.59/0.61    spl7_9 <=> v1_funct_2(sK4,sK2,sK1)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.59/0.61  fof(f155,plain,(
% 1.59/0.61    spl7_10 <=> v1_funct_1(sK4)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.59/0.61  fof(f140,plain,(
% 1.59/0.61    spl7_7 <=> v1_xboole_0(sK3)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.59/0.61  fof(f120,plain,(
% 1.59/0.61    spl7_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.59/0.61  fof(f125,plain,(
% 1.59/0.61    spl7_4 <=> v1_xboole_0(sK2)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.59/0.61  fof(f115,plain,(
% 1.59/0.61    spl7_2 <=> v1_xboole_0(sK1)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.59/0.61  fof(f949,plain,(
% 1.59/0.61    spl7_119 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_119])])).
% 1.59/0.61  fof(f1580,plain,(
% 1.59/0.61    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_36 | ~spl7_44 | ~spl7_45 | ~spl7_119 | ~spl7_125 | ~spl7_130)),
% 1.59/0.61    inference(trivial_inequality_removal,[],[f1579])).
% 1.59/0.61  fof(f1579,plain,(
% 1.59/0.61    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_36 | ~spl7_44 | ~spl7_45 | ~spl7_119 | ~spl7_125 | ~spl7_130)),
% 1.59/0.61    inference(forward_demodulation,[],[f1578,f1003])).
% 1.59/0.61  fof(f1003,plain,(
% 1.59/0.61    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | ~spl7_125),
% 1.59/0.61    inference(avatar_component_clause,[],[f1001])).
% 1.59/0.61  fof(f1578,plain,(
% 1.59/0.61    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_36 | ~spl7_44 | ~spl7_45 | ~spl7_119 | ~spl7_130)),
% 1.59/0.61    inference(forward_demodulation,[],[f1577,f1041])).
% 1.59/0.61  fof(f1577,plain,(
% 1.59/0.61    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_36 | ~spl7_44 | ~spl7_45 | ~spl7_119)),
% 1.59/0.61    inference(forward_demodulation,[],[f1576,f422])).
% 1.59/0.61  fof(f1576,plain,(
% 1.59/0.61    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_36 | ~spl7_45 | ~spl7_119)),
% 1.59/0.61    inference(forward_demodulation,[],[f1575,f318])).
% 1.59/0.61  fof(f1575,plain,(
% 1.59/0.61    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_45 | ~spl7_119)),
% 1.59/0.61    inference(forward_demodulation,[],[f1574,f369])).
% 1.59/0.61  fof(f1574,plain,(
% 1.59/0.61    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_45 | ~spl7_119)),
% 1.59/0.61    inference(forward_demodulation,[],[f1549,f426])).
% 1.59/0.61  fof(f1549,plain,(
% 1.59/0.61    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~spl7_119),
% 1.59/0.61    inference(resolution,[],[f951,f106])).
% 1.59/0.61  fof(f106,plain,(
% 1.59/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 1.59/0.61    inference(equality_resolution,[],[f72])).
% 1.59/0.61  fof(f72,plain,(
% 1.59/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.59/0.61    inference(cnf_transformation,[],[f30])).
% 1.59/0.61  fof(f30,plain,(
% 1.59/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.59/0.61    inference(flattening,[],[f29])).
% 1.59/0.61  fof(f29,plain,(
% 1.59/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.59/0.61    inference(ennf_transformation,[],[f21])).
% 1.59/0.61  fof(f21,axiom,(
% 1.59/0.61    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).
% 1.59/0.61  fof(f951,plain,(
% 1.59/0.61    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl7_119),
% 1.59/0.61    inference(avatar_component_clause,[],[f949])).
% 1.59/0.61  fof(f1573,plain,(
% 1.59/0.61    spl7_15 | spl7_1 | ~spl7_115 | ~spl7_106 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_6 | spl7_7 | ~spl7_3 | spl7_4 | spl7_2 | ~spl7_6 | ~spl7_36 | ~spl7_44 | ~spl7_45 | ~spl7_119 | ~spl7_125 | ~spl7_130),
% 1.59/0.61    inference(avatar_split_clause,[],[f1572,f1039,f1001,f949,f425,f421,f316,f135,f115,f125,f120,f140,f135,f155,f150,f145,f170,f165,f160,f847,f914,f110,f179])).
% 1.59/0.61  fof(f179,plain,(
% 1.59/0.61    spl7_15 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.59/0.61  fof(f1572,plain,(
% 1.59/0.61    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_36 | ~spl7_44 | ~spl7_45 | ~spl7_119 | ~spl7_125 | ~spl7_130)),
% 1.59/0.61    inference(trivial_inequality_removal,[],[f1571])).
% 1.59/0.61  fof(f1571,plain,(
% 1.59/0.61    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_36 | ~spl7_44 | ~spl7_45 | ~spl7_119 | ~spl7_125 | ~spl7_130)),
% 1.59/0.61    inference(forward_demodulation,[],[f1570,f1003])).
% 1.59/0.61  fof(f1570,plain,(
% 1.59/0.61    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_36 | ~spl7_44 | ~spl7_45 | ~spl7_119 | ~spl7_130)),
% 1.59/0.61    inference(forward_demodulation,[],[f1569,f1041])).
% 1.59/0.61  fof(f1569,plain,(
% 1.59/0.61    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_36 | ~spl7_44 | ~spl7_45 | ~spl7_119)),
% 1.59/0.61    inference(forward_demodulation,[],[f1568,f422])).
% 1.59/0.61  fof(f1568,plain,(
% 1.59/0.61    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_36 | ~spl7_45 | ~spl7_119)),
% 1.59/0.61    inference(forward_demodulation,[],[f1567,f318])).
% 1.59/0.61  fof(f1567,plain,(
% 1.59/0.61    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_45 | ~spl7_119)),
% 1.59/0.61    inference(forward_demodulation,[],[f1566,f369])).
% 1.59/0.61  fof(f1566,plain,(
% 1.59/0.61    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_45 | ~spl7_119)),
% 1.59/0.61    inference(forward_demodulation,[],[f1548,f426])).
% 1.59/0.61  fof(f1548,plain,(
% 1.59/0.61    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~spl7_119),
% 1.59/0.61    inference(resolution,[],[f951,f107])).
% 1.59/0.61  fof(f107,plain,(
% 1.59/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 1.59/0.61    inference(equality_resolution,[],[f71])).
% 1.59/0.61  fof(f71,plain,(
% 1.59/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.59/0.61    inference(cnf_transformation,[],[f30])).
% 1.59/0.61  fof(f1042,plain,(
% 1.59/0.61    spl7_130 | ~spl7_48 | ~spl7_129),
% 1.59/0.61    inference(avatar_split_clause,[],[f1034,f1027,f447,f1039])).
% 1.59/0.61  fof(f447,plain,(
% 1.59/0.61    spl7_48 <=> ! [X0] : (~r1_xboole_0(sK2,X0) | k1_xboole_0 = k7_relat_1(sK4,X0))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 1.59/0.61  fof(f1027,plain,(
% 1.59/0.61    spl7_129 <=> r1_xboole_0(sK2,k1_xboole_0)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_129])])).
% 1.59/0.61  fof(f1034,plain,(
% 1.59/0.61    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | (~spl7_48 | ~spl7_129)),
% 1.59/0.61    inference(resolution,[],[f1029,f448])).
% 1.59/0.61  fof(f448,plain,(
% 1.59/0.61    ( ! [X0] : (~r1_xboole_0(sK2,X0) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl7_48),
% 1.59/0.61    inference(avatar_component_clause,[],[f447])).
% 1.59/0.61  fof(f1029,plain,(
% 1.59/0.61    r1_xboole_0(sK2,k1_xboole_0) | ~spl7_129),
% 1.59/0.61    inference(avatar_component_clause,[],[f1027])).
% 1.59/0.61  fof(f1030,plain,(
% 1.59/0.61    spl7_129 | ~spl7_23 | ~spl7_42 | ~spl7_122),
% 1.59/0.61    inference(avatar_split_clause,[],[f1025,f969,f408,f222,f1027])).
% 1.59/0.61  fof(f222,plain,(
% 1.59/0.61    spl7_23 <=> v1_relat_1(sK4)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 1.59/0.61  fof(f408,plain,(
% 1.59/0.61    spl7_42 <=> sK2 = k1_relat_1(sK4)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 1.59/0.61  fof(f969,plain,(
% 1.59/0.61    spl7_122 <=> k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_122])])).
% 1.59/0.61  fof(f1025,plain,(
% 1.59/0.61    r1_xboole_0(sK2,k1_xboole_0) | (~spl7_23 | ~spl7_42 | ~spl7_122)),
% 1.59/0.61    inference(trivial_inequality_removal,[],[f1024])).
% 1.59/0.61  fof(f1024,plain,(
% 1.59/0.61    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK2,k1_xboole_0) | (~spl7_23 | ~spl7_42 | ~spl7_122)),
% 1.59/0.61    inference(superposition,[],[f429,f971])).
% 1.59/0.61  fof(f971,plain,(
% 1.59/0.61    k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0) | ~spl7_122),
% 1.59/0.61    inference(avatar_component_clause,[],[f969])).
% 1.59/0.61  fof(f429,plain,(
% 1.59/0.61    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK4,X0) | r1_xboole_0(sK2,X0)) ) | (~spl7_23 | ~spl7_42)),
% 1.59/0.61    inference(backward_demodulation,[],[f343,f410])).
% 1.59/0.61  fof(f410,plain,(
% 1.59/0.61    sK2 = k1_relat_1(sK4) | ~spl7_42),
% 1.59/0.61    inference(avatar_component_clause,[],[f408])).
% 1.59/0.61  fof(f343,plain,(
% 1.59/0.61    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK4,X0) | r1_xboole_0(k1_relat_1(sK4),X0)) ) | ~spl7_23),
% 1.59/0.61    inference(resolution,[],[f85,f224])).
% 1.59/0.61  fof(f224,plain,(
% 1.59/0.61    v1_relat_1(sK4) | ~spl7_23),
% 1.59/0.61    inference(avatar_component_clause,[],[f222])).
% 1.59/0.61  fof(f85,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f41])).
% 1.59/0.61  fof(f41,plain,(
% 1.59/0.61    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(ennf_transformation,[],[f8])).
% 1.59/0.61  fof(f8,axiom,(
% 1.59/0.61    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 1.59/0.61  fof(f1004,plain,(
% 1.59/0.61    spl7_125 | ~spl7_61 | ~spl7_124),
% 1.59/0.61    inference(avatar_split_clause,[],[f996,f989,f521,f1001])).
% 1.59/0.61  fof(f521,plain,(
% 1.59/0.61    spl7_61 <=> ! [X0] : (~r1_xboole_0(sK3,X0) | k1_xboole_0 = k7_relat_1(sK5,X0))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).
% 1.59/0.61  fof(f989,plain,(
% 1.59/0.61    spl7_124 <=> r1_xboole_0(sK3,k1_xboole_0)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).
% 1.59/0.61  fof(f996,plain,(
% 1.59/0.61    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | (~spl7_61 | ~spl7_124)),
% 1.59/0.61    inference(resolution,[],[f991,f522])).
% 1.59/0.61  fof(f522,plain,(
% 1.59/0.61    ( ! [X0] : (~r1_xboole_0(sK3,X0) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl7_61),
% 1.59/0.61    inference(avatar_component_clause,[],[f521])).
% 1.59/0.61  fof(f991,plain,(
% 1.59/0.61    r1_xboole_0(sK3,k1_xboole_0) | ~spl7_124),
% 1.59/0.61    inference(avatar_component_clause,[],[f989])).
% 1.59/0.61  fof(f992,plain,(
% 1.59/0.61    spl7_124 | ~spl7_24 | ~spl7_43 | ~spl7_123),
% 1.59/0.61    inference(avatar_split_clause,[],[f987,f979,f414,f227,f989])).
% 1.59/0.61  fof(f227,plain,(
% 1.59/0.61    spl7_24 <=> v1_relat_1(sK5)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 1.59/0.61  fof(f414,plain,(
% 1.59/0.61    spl7_43 <=> sK3 = k1_relat_1(sK5)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 1.59/0.61  fof(f979,plain,(
% 1.59/0.61    spl7_123 <=> k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_123])])).
% 1.59/0.61  fof(f987,plain,(
% 1.59/0.61    r1_xboole_0(sK3,k1_xboole_0) | (~spl7_24 | ~spl7_43 | ~spl7_123)),
% 1.59/0.61    inference(trivial_inequality_removal,[],[f986])).
% 1.59/0.61  fof(f986,plain,(
% 1.59/0.61    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK3,k1_xboole_0) | (~spl7_24 | ~spl7_43 | ~spl7_123)),
% 1.59/0.61    inference(superposition,[],[f503,f981])).
% 1.59/0.61  fof(f981,plain,(
% 1.59/0.61    k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0) | ~spl7_123),
% 1.59/0.61    inference(avatar_component_clause,[],[f979])).
% 1.59/0.61  fof(f503,plain,(
% 1.59/0.61    ( ! [X1] : (k1_xboole_0 != k9_relat_1(sK5,X1) | r1_xboole_0(sK3,X1)) ) | (~spl7_24 | ~spl7_43)),
% 1.59/0.61    inference(backward_demodulation,[],[f344,f416])).
% 1.59/0.61  fof(f416,plain,(
% 1.59/0.61    sK3 = k1_relat_1(sK5) | ~spl7_43),
% 1.59/0.61    inference(avatar_component_clause,[],[f414])).
% 1.59/0.61  fof(f344,plain,(
% 1.59/0.61    ( ! [X1] : (k1_xboole_0 != k9_relat_1(sK5,X1) | r1_xboole_0(k1_relat_1(sK5),X1)) ) | ~spl7_24),
% 1.59/0.61    inference(resolution,[],[f85,f229])).
% 1.59/0.61  fof(f229,plain,(
% 1.59/0.61    v1_relat_1(sK5) | ~spl7_24),
% 1.59/0.61    inference(avatar_component_clause,[],[f227])).
% 1.59/0.61  fof(f984,plain,(
% 1.59/0.61    spl7_123 | ~spl7_24 | ~spl7_68 | ~spl7_107),
% 1.59/0.61    inference(avatar_split_clause,[],[f983,f856,f569,f227,f979])).
% 1.59/0.61  fof(f569,plain,(
% 1.59/0.61    spl7_68 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).
% 1.59/0.61  fof(f856,plain,(
% 1.59/0.61    spl7_107 <=> k1_xboole_0 = k7_relat_1(sK5,sK2)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_107])])).
% 1.59/0.61  fof(f983,plain,(
% 1.59/0.61    k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0) | (~spl7_24 | ~spl7_68 | ~spl7_107)),
% 1.59/0.61    inference(forward_demodulation,[],[f976,f571])).
% 1.59/0.61  fof(f571,plain,(
% 1.59/0.61    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | ~spl7_68),
% 1.59/0.61    inference(avatar_component_clause,[],[f569])).
% 1.59/0.61  fof(f976,plain,(
% 1.59/0.61    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0) | (~spl7_24 | ~spl7_107)),
% 1.59/0.61    inference(superposition,[],[f827,f858])).
% 1.59/0.61  fof(f858,plain,(
% 1.59/0.61    k1_xboole_0 = k7_relat_1(sK5,sK2) | ~spl7_107),
% 1.59/0.61    inference(avatar_component_clause,[],[f856])).
% 1.59/0.61  fof(f827,plain,(
% 1.59/0.61    ( ! [X0] : (k9_relat_1(k7_relat_1(sK5,X0),k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0)) ) | ~spl7_24),
% 1.59/0.61    inference(resolution,[],[f373,f70])).
% 1.59/0.61  fof(f70,plain,(
% 1.59/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f2])).
% 1.59/0.61  fof(f2,axiom,(
% 1.59/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.59/0.61  fof(f373,plain,(
% 1.59/0.61    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k9_relat_1(k7_relat_1(sK5,X3),X2) = k9_relat_1(sK5,X2)) ) | ~spl7_24),
% 1.59/0.61    inference(resolution,[],[f78,f229])).
% 1.59/0.61  fof(f78,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f35])).
% 1.59/0.61  fof(f35,plain,(
% 1.59/0.61    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 1.59/0.61    inference(ennf_transformation,[],[f9])).
% 1.59/0.61  fof(f9,axiom,(
% 1.59/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 1.59/0.61  fof(f972,plain,(
% 1.59/0.61    spl7_122 | ~spl7_23 | ~spl7_64 | ~spl7_68),
% 1.59/0.61    inference(avatar_split_clause,[],[f967,f569,f536,f222,f969])).
% 1.59/0.61  fof(f536,plain,(
% 1.59/0.61    spl7_64 <=> k1_xboole_0 = k7_relat_1(sK4,sK3)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).
% 1.59/0.61  fof(f967,plain,(
% 1.59/0.61    k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0) | (~spl7_23 | ~spl7_64 | ~spl7_68)),
% 1.59/0.61    inference(forward_demodulation,[],[f965,f571])).
% 1.59/0.61  fof(f965,plain,(
% 1.59/0.61    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0) | (~spl7_23 | ~spl7_64)),
% 1.59/0.61    inference(superposition,[],[f822,f538])).
% 1.59/0.61  fof(f538,plain,(
% 1.59/0.61    k1_xboole_0 = k7_relat_1(sK4,sK3) | ~spl7_64),
% 1.59/0.61    inference(avatar_component_clause,[],[f536])).
% 1.59/0.61  fof(f822,plain,(
% 1.59/0.61    ( ! [X0] : (k9_relat_1(sK4,k1_xboole_0) = k9_relat_1(k7_relat_1(sK4,X0),k1_xboole_0)) ) | ~spl7_23),
% 1.59/0.61    inference(resolution,[],[f372,f70])).
% 1.59/0.61  fof(f372,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k9_relat_1(sK4,X0) = k9_relat_1(k7_relat_1(sK4,X1),X0)) ) | ~spl7_23),
% 1.59/0.61    inference(resolution,[],[f78,f224])).
% 1.59/0.61  fof(f952,plain,(
% 1.59/0.61    spl7_119 | ~spl7_10 | ~spl7_9 | ~spl7_8 | ~spl7_99),
% 1.59/0.61    inference(avatar_split_clause,[],[f947,f789,f145,f150,f155,f949])).
% 1.59/0.61  fof(f789,plain,(
% 1.59/0.61    spl7_99 <=> ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_99])])).
% 1.59/0.61  fof(f947,plain,(
% 1.59/0.61    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl7_8 | ~spl7_99)),
% 1.59/0.61    inference(resolution,[],[f790,f147])).
% 1.59/0.61  fof(f147,plain,(
% 1.59/0.61    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl7_8),
% 1.59/0.61    inference(avatar_component_clause,[],[f145])).
% 1.59/0.61  fof(f790,plain,(
% 1.59/0.61    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))) ) | ~spl7_99),
% 1.59/0.61    inference(avatar_component_clause,[],[f789])).
% 1.59/0.61  fof(f917,plain,(
% 1.59/0.61    spl7_115 | ~spl7_10 | ~spl7_9 | ~spl7_8 | ~spl7_95),
% 1.59/0.61    inference(avatar_split_clause,[],[f912,f769,f145,f150,f155,f914])).
% 1.59/0.61  fof(f769,plain,(
% 1.59/0.61    spl7_95 <=> ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).
% 1.59/0.61  fof(f912,plain,(
% 1.59/0.61    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl7_8 | ~spl7_95)),
% 1.59/0.61    inference(resolution,[],[f770,f147])).
% 1.59/0.61  fof(f770,plain,(
% 1.59/0.61    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)) ) | ~spl7_95),
% 1.59/0.61    inference(avatar_component_clause,[],[f769])).
% 1.59/0.61  fof(f859,plain,(
% 1.59/0.61    spl7_107 | ~spl7_35 | ~spl7_63),
% 1.59/0.61    inference(avatar_split_clause,[],[f853,f529,f309,f856])).
% 1.59/0.61  fof(f309,plain,(
% 1.59/0.61    spl7_35 <=> r1_xboole_0(sK2,sK3)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 1.59/0.61  fof(f529,plain,(
% 1.59/0.61    spl7_63 <=> ! [X2] : (~r1_xboole_0(X2,sK3) | k1_xboole_0 = k7_relat_1(sK5,X2))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).
% 1.59/0.61  fof(f853,plain,(
% 1.59/0.61    k1_xboole_0 = k7_relat_1(sK5,sK2) | (~spl7_35 | ~spl7_63)),
% 1.59/0.61    inference(resolution,[],[f530,f311])).
% 1.59/0.61  fof(f311,plain,(
% 1.59/0.61    r1_xboole_0(sK2,sK3) | ~spl7_35),
% 1.59/0.61    inference(avatar_component_clause,[],[f309])).
% 1.59/0.61  fof(f530,plain,(
% 1.59/0.61    ( ! [X2] : (~r1_xboole_0(X2,sK3) | k1_xboole_0 = k7_relat_1(sK5,X2)) ) | ~spl7_63),
% 1.59/0.61    inference(avatar_component_clause,[],[f529])).
% 1.59/0.61  fof(f850,plain,(
% 1.59/0.61    spl7_106 | ~spl7_10 | ~spl7_9 | ~spl7_8 | ~spl7_79),
% 1.59/0.61    inference(avatar_split_clause,[],[f845,f676,f145,f150,f155,f847])).
% 1.59/0.61  fof(f676,plain,(
% 1.59/0.61    spl7_79 <=> ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).
% 1.59/0.61  fof(f845,plain,(
% 1.59/0.61    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl7_8 | ~spl7_79)),
% 1.59/0.61    inference(resolution,[],[f677,f147])).
% 1.59/0.61  fof(f677,plain,(
% 1.59/0.61    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))) ) | ~spl7_79),
% 1.59/0.61    inference(avatar_component_clause,[],[f676])).
% 1.59/0.61  fof(f791,plain,(
% 1.59/0.61    ~spl7_6 | ~spl7_12 | spl7_7 | ~spl7_13 | spl7_2 | spl7_99 | ~spl7_11 | ~spl7_57),
% 1.59/0.61    inference(avatar_split_clause,[],[f783,f495,f160,f789,f115,f170,f140,f165,f135])).
% 1.59/0.61  fof(f495,plain,(
% 1.59/0.61    spl7_57 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).
% 1.59/0.61  fof(f783,plain,(
% 1.59/0.61    ( ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl7_11 | ~spl7_57)),
% 1.59/0.61    inference(resolution,[],[f496,f162])).
% 1.59/0.61  fof(f162,plain,(
% 1.59/0.61    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl7_11),
% 1.59/0.61    inference(avatar_component_clause,[],[f160])).
% 1.59/0.61  fof(f496,plain,(
% 1.59/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl7_57),
% 1.59/0.61    inference(avatar_component_clause,[],[f495])).
% 1.59/0.61  fof(f771,plain,(
% 1.59/0.61    ~spl7_6 | ~spl7_12 | spl7_7 | ~spl7_13 | spl7_2 | spl7_95 | ~spl7_11 | ~spl7_55),
% 1.59/0.61    inference(avatar_split_clause,[],[f763,f483,f160,f769,f115,f170,f140,f165,f135])).
% 1.59/0.61  fof(f483,plain,(
% 1.59/0.61    spl7_55 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).
% 1.59/0.61  fof(f763,plain,(
% 1.59/0.61    ( ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl7_11 | ~spl7_55)),
% 1.59/0.61    inference(resolution,[],[f484,f162])).
% 1.59/0.61  fof(f484,plain,(
% 1.59/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl7_55),
% 1.59/0.61    inference(avatar_component_clause,[],[f483])).
% 1.59/0.61  fof(f678,plain,(
% 1.59/0.61    ~spl7_6 | ~spl7_12 | spl7_7 | ~spl7_13 | spl7_2 | spl7_79 | ~spl7_11 | ~spl7_51),
% 1.59/0.61    inference(avatar_split_clause,[],[f670,f463,f160,f676,f115,f170,f140,f165,f135])).
% 1.59/0.61  fof(f463,plain,(
% 1.59/0.61    spl7_51 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).
% 1.59/0.61  fof(f670,plain,(
% 1.59/0.61    ( ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl7_11 | ~spl7_51)),
% 1.59/0.61    inference(resolution,[],[f464,f162])).
% 1.59/0.61  fof(f464,plain,(
% 1.59/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl7_51),
% 1.59/0.61    inference(avatar_component_clause,[],[f463])).
% 1.59/0.61  fof(f572,plain,(
% 1.59/0.61    spl7_68 | ~spl7_17 | ~spl7_18 | ~spl7_38),
% 1.59/0.61    inference(avatar_split_clause,[],[f567,f326,f193,f188,f569])).
% 1.59/0.61  fof(f188,plain,(
% 1.59/0.61    spl7_17 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.59/0.61  fof(f193,plain,(
% 1.59/0.61    spl7_18 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 1.59/0.61  fof(f326,plain,(
% 1.59/0.61    spl7_38 <=> v1_relat_1(k1_xboole_0)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 1.59/0.61  fof(f567,plain,(
% 1.59/0.61    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | (~spl7_17 | ~spl7_18 | ~spl7_38)),
% 1.59/0.61    inference(forward_demodulation,[],[f566,f190])).
% 1.59/0.61  fof(f190,plain,(
% 1.59/0.61    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl7_17),
% 1.59/0.61    inference(avatar_component_clause,[],[f188])).
% 1.59/0.61  fof(f566,plain,(
% 1.59/0.61    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) | (~spl7_18 | ~spl7_38)),
% 1.59/0.61    inference(forward_demodulation,[],[f559,f195])).
% 1.59/0.61  fof(f195,plain,(
% 1.59/0.61    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_18),
% 1.59/0.61    inference(avatar_component_clause,[],[f193])).
% 1.59/0.61  fof(f559,plain,(
% 1.59/0.61    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) | ~spl7_38),
% 1.59/0.61    inference(resolution,[],[f327,f74])).
% 1.59/0.61  fof(f74,plain,(
% 1.59/0.61    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f31])).
% 1.59/0.61  fof(f31,plain,(
% 1.59/0.61    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.59/0.61    inference(ennf_transformation,[],[f7])).
% 1.59/0.61  fof(f7,axiom,(
% 1.59/0.61    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.59/0.61  fof(f327,plain,(
% 1.59/0.61    v1_relat_1(k1_xboole_0) | ~spl7_38),
% 1.59/0.61    inference(avatar_component_clause,[],[f326])).
% 1.59/0.61  fof(f546,plain,(
% 1.59/0.61    spl7_38 | ~spl7_23 | ~spl7_64),
% 1.59/0.61    inference(avatar_split_clause,[],[f544,f536,f222,f326])).
% 1.59/0.61  fof(f544,plain,(
% 1.59/0.61    v1_relat_1(k1_xboole_0) | (~spl7_23 | ~spl7_64)),
% 1.59/0.61    inference(superposition,[],[f231,f538])).
% 1.59/0.61  fof(f231,plain,(
% 1.59/0.61    ( ! [X0] : (v1_relat_1(k7_relat_1(sK4,X0))) ) | ~spl7_23),
% 1.59/0.61    inference(resolution,[],[f224,f83])).
% 1.59/0.61  fof(f83,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f40])).
% 1.59/0.61  fof(f40,plain,(
% 1.59/0.61    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.59/0.61    inference(ennf_transformation,[],[f6])).
% 1.59/0.61  fof(f6,axiom,(
% 1.59/0.61    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.59/0.61  fof(f539,plain,(
% 1.59/0.61    spl7_64 | ~spl7_35 | ~spl7_48),
% 1.59/0.61    inference(avatar_split_clause,[],[f534,f447,f309,f536])).
% 1.59/0.61  fof(f534,plain,(
% 1.59/0.61    k1_xboole_0 = k7_relat_1(sK4,sK3) | (~spl7_35 | ~spl7_48)),
% 1.59/0.61    inference(resolution,[],[f448,f311])).
% 1.59/0.61  fof(f531,plain,(
% 1.59/0.61    ~spl7_24 | spl7_63 | ~spl7_43),
% 1.59/0.61    inference(avatar_split_clause,[],[f508,f414,f529,f227])).
% 1.59/0.61  fof(f508,plain,(
% 1.59/0.61    ( ! [X2] : (~r1_xboole_0(X2,sK3) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X2)) ) | ~spl7_43),
% 1.59/0.61    inference(superposition,[],[f77,f416])).
% 1.59/0.61  fof(f77,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f34])).
% 1.59/0.61  fof(f34,plain,(
% 1.59/0.61    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.59/0.61    inference(ennf_transformation,[],[f10])).
% 1.59/0.61  fof(f10,axiom,(
% 1.59/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 1.59/0.61  fof(f523,plain,(
% 1.59/0.61    ~spl7_24 | spl7_61 | ~spl7_43),
% 1.59/0.61    inference(avatar_split_clause,[],[f506,f414,f521,f227])).
% 1.59/0.61  fof(f506,plain,(
% 1.59/0.61    ( ! [X0] : (~r1_xboole_0(sK3,X0) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl7_43),
% 1.59/0.61    inference(superposition,[],[f86,f416])).
% 1.59/0.61  fof(f86,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f42])).
% 1.59/0.61  fof(f42,plain,(
% 1.59/0.61    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(ennf_transformation,[],[f13])).
% 1.59/0.61  fof(f13,axiom,(
% 1.59/0.61    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 1.59/0.61  fof(f497,plain,(
% 1.59/0.61    spl7_1 | spl7_4 | spl7_57 | ~spl7_3),
% 1.59/0.61    inference(avatar_split_clause,[],[f490,f120,f495,f125,f110])).
% 1.59/0.61  fof(f490,plain,(
% 1.59/0.61    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0)))) ) | ~spl7_3),
% 1.59/0.61    inference(resolution,[],[f100,f122])).
% 1.59/0.61  fof(f122,plain,(
% 1.59/0.61    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl7_3),
% 1.59/0.61    inference(avatar_component_clause,[],[f120])).
% 1.59/0.61  fof(f100,plain,(
% 1.59/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f53])).
% 1.59/0.61  fof(f53,plain,(
% 1.59/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.59/0.61    inference(flattening,[],[f52])).
% 1.59/0.61  fof(f52,plain,(
% 1.59/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.59/0.61    inference(ennf_transformation,[],[f22])).
% 1.59/0.61  fof(f22,axiom,(
% 1.59/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 1.59/0.61  fof(f485,plain,(
% 1.59/0.61    spl7_1 | spl7_4 | spl7_55 | ~spl7_3),
% 1.59/0.61    inference(avatar_split_clause,[],[f478,f120,f483,f125,f110])).
% 1.59/0.61  fof(f478,plain,(
% 1.59/0.61    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0)) ) | ~spl7_3),
% 1.59/0.61    inference(resolution,[],[f99,f122])).
% 1.59/0.61  fof(f99,plain,(
% 1.59/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f53])).
% 1.59/0.61  fof(f465,plain,(
% 1.59/0.61    spl7_1 | spl7_4 | spl7_51 | ~spl7_3),
% 1.59/0.61    inference(avatar_split_clause,[],[f458,f120,f463,f125,f110])).
% 1.59/0.61  fof(f458,plain,(
% 1.59/0.61    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3))) ) | ~spl7_3),
% 1.59/0.61    inference(resolution,[],[f98,f122])).
% 1.59/0.61  fof(f98,plain,(
% 1.59/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f53])).
% 1.59/0.61  fof(f449,plain,(
% 1.59/0.61    ~spl7_23 | spl7_48 | ~spl7_42),
% 1.59/0.61    inference(avatar_split_clause,[],[f432,f408,f447,f222])).
% 1.59/0.61  fof(f432,plain,(
% 1.59/0.61    ( ! [X0] : (~r1_xboole_0(sK2,X0) | ~v1_relat_1(sK4) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl7_42),
% 1.59/0.61    inference(superposition,[],[f86,f410])).
% 1.59/0.61  fof(f427,plain,(
% 1.59/0.61    spl7_45 | ~spl7_13 | ~spl7_11),
% 1.59/0.61    inference(avatar_split_clause,[],[f419,f160,f170,f425])).
% 1.59/0.61  fof(f419,plain,(
% 1.59/0.61    ( ! [X1] : (~v1_funct_1(sK5) | k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl7_11),
% 1.59/0.61    inference(resolution,[],[f97,f162])).
% 1.59/0.61  fof(f97,plain,(
% 1.59/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f51])).
% 1.59/0.61  fof(f51,plain,(
% 1.59/0.61    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.59/0.61    inference(flattening,[],[f50])).
% 1.59/0.61  fof(f50,plain,(
% 1.59/0.61    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.59/0.61    inference(ennf_transformation,[],[f20])).
% 1.59/0.61  fof(f20,axiom,(
% 1.59/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.59/0.61  fof(f423,plain,(
% 1.59/0.61    spl7_44 | ~spl7_10 | ~spl7_8),
% 1.59/0.61    inference(avatar_split_clause,[],[f418,f145,f155,f421])).
% 1.59/0.61  fof(f418,plain,(
% 1.59/0.61    ( ! [X0] : (~v1_funct_1(sK4) | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl7_8),
% 1.59/0.61    inference(resolution,[],[f97,f147])).
% 1.59/0.61  fof(f417,plain,(
% 1.59/0.61    ~spl7_24 | spl7_43 | ~spl7_34 | ~spl7_41),
% 1.59/0.61    inference(avatar_split_clause,[],[f412,f402,f293,f414,f227])).
% 1.59/0.61  fof(f293,plain,(
% 1.59/0.61    spl7_34 <=> v4_relat_1(sK5,sK3)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 1.59/0.61  fof(f402,plain,(
% 1.59/0.61    spl7_41 <=> v1_partfun1(sK5,sK3)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 1.59/0.61  fof(f412,plain,(
% 1.59/0.61    ~v4_relat_1(sK5,sK3) | sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5) | ~spl7_41),
% 1.59/0.61    inference(resolution,[],[f404,f91])).
% 1.59/0.61  fof(f91,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f46])).
% 1.59/0.62  fof(f46,plain,(
% 1.59/0.62    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.59/0.62    inference(flattening,[],[f45])).
% 1.59/0.62  fof(f45,plain,(
% 1.59/0.62    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.59/0.62    inference(ennf_transformation,[],[f19])).
% 1.59/0.62  fof(f19,axiom,(
% 1.59/0.62    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 1.59/0.62  fof(f404,plain,(
% 1.59/0.62    v1_partfun1(sK5,sK3) | ~spl7_41),
% 1.59/0.62    inference(avatar_component_clause,[],[f402])).
% 1.59/0.62  fof(f411,plain,(
% 1.59/0.62    ~spl7_23 | spl7_42 | ~spl7_33 | ~spl7_40),
% 1.59/0.62    inference(avatar_split_clause,[],[f406,f397,f288,f408,f222])).
% 1.59/0.62  fof(f288,plain,(
% 1.59/0.62    spl7_33 <=> v4_relat_1(sK4,sK2)),
% 1.59/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 1.59/0.62  fof(f397,plain,(
% 1.59/0.62    spl7_40 <=> v1_partfun1(sK4,sK2)),
% 1.59/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 1.59/0.62  fof(f406,plain,(
% 1.59/0.62    ~v4_relat_1(sK4,sK2) | sK2 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl7_40),
% 1.59/0.62    inference(resolution,[],[f399,f91])).
% 1.59/0.62  fof(f399,plain,(
% 1.59/0.62    v1_partfun1(sK4,sK2) | ~spl7_40),
% 1.59/0.62    inference(avatar_component_clause,[],[f397])).
% 1.59/0.62  fof(f405,plain,(
% 1.59/0.62    spl7_41 | ~spl7_12 | ~spl7_13 | spl7_2 | ~spl7_11),
% 1.59/0.62    inference(avatar_split_clause,[],[f395,f160,f115,f170,f165,f402])).
% 1.59/0.62  fof(f395,plain,(
% 1.59/0.62    v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3) | ~spl7_11),
% 1.59/0.62    inference(resolution,[],[f82,f162])).
% 1.59/0.62  fof(f82,plain,(
% 1.59/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f39])).
% 1.59/0.62  fof(f39,plain,(
% 1.59/0.62    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.59/0.62    inference(flattening,[],[f38])).
% 1.59/0.62  fof(f38,plain,(
% 1.59/0.62    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.59/0.62    inference(ennf_transformation,[],[f18])).
% 1.59/0.62  fof(f18,axiom,(
% 1.59/0.62    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.59/0.62  fof(f400,plain,(
% 1.59/0.62    spl7_40 | ~spl7_9 | ~spl7_10 | spl7_2 | ~spl7_8),
% 1.59/0.62    inference(avatar_split_clause,[],[f394,f145,f115,f155,f150,f397])).
% 1.59/0.62  fof(f394,plain,(
% 1.59/0.62    v1_xboole_0(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2) | ~spl7_8),
% 1.59/0.62    inference(resolution,[],[f82,f147])).
% 1.59/0.62  fof(f319,plain,(
% 1.59/0.62    spl7_36 | ~spl7_35),
% 1.59/0.62    inference(avatar_split_clause,[],[f314,f309,f316])).
% 1.59/0.62  fof(f314,plain,(
% 1.59/0.62    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl7_35),
% 1.59/0.62    inference(resolution,[],[f311,f101])).
% 1.59/0.62  fof(f101,plain,(
% 1.59/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.59/0.62    inference(definition_unfolding,[],[f93,f81])).
% 1.59/0.62  fof(f93,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f1])).
% 1.59/0.62  fof(f1,axiom,(
% 1.59/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.59/0.62  fof(f312,plain,(
% 1.59/0.62    spl7_4 | spl7_35 | spl7_7 | ~spl7_5),
% 1.59/0.62    inference(avatar_split_clause,[],[f307,f130,f140,f309,f125])).
% 1.59/0.62  fof(f130,plain,(
% 1.59/0.62    spl7_5 <=> r1_subset_1(sK2,sK3)),
% 1.59/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.59/0.62  fof(f307,plain,(
% 1.59/0.62    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | ~spl7_5),
% 1.59/0.62    inference(resolution,[],[f89,f132])).
% 1.59/0.62  fof(f132,plain,(
% 1.59/0.62    r1_subset_1(sK2,sK3) | ~spl7_5),
% 1.59/0.62    inference(avatar_component_clause,[],[f130])).
% 1.59/0.62  fof(f89,plain,(
% 1.59/0.62    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f44])).
% 1.59/0.62  fof(f44,plain,(
% 1.59/0.62    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.59/0.62    inference(flattening,[],[f43])).
% 1.59/0.62  fof(f43,plain,(
% 1.59/0.62    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.59/0.62    inference(ennf_transformation,[],[f14])).
% 1.59/0.62  fof(f14,axiom,(
% 1.59/0.62    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 1.59/0.62  fof(f296,plain,(
% 1.59/0.62    spl7_34 | ~spl7_11),
% 1.59/0.62    inference(avatar_split_clause,[],[f286,f160,f293])).
% 1.59/0.62  fof(f286,plain,(
% 1.59/0.62    v4_relat_1(sK5,sK3) | ~spl7_11),
% 1.59/0.62    inference(resolution,[],[f96,f162])).
% 1.59/0.62  fof(f96,plain,(
% 1.59/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f49])).
% 1.59/0.62  fof(f49,plain,(
% 1.59/0.62    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.62    inference(ennf_transformation,[],[f26])).
% 1.59/0.62  fof(f26,plain,(
% 1.59/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.59/0.62    inference(pure_predicate_removal,[],[f16])).
% 1.59/0.62  fof(f16,axiom,(
% 1.59/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.59/0.62  fof(f291,plain,(
% 1.59/0.62    spl7_33 | ~spl7_8),
% 1.59/0.62    inference(avatar_split_clause,[],[f285,f145,f288])).
% 1.59/0.62  fof(f285,plain,(
% 1.59/0.62    v4_relat_1(sK4,sK2) | ~spl7_8),
% 1.59/0.62    inference(resolution,[],[f96,f147])).
% 1.59/0.62  fof(f230,plain,(
% 1.59/0.62    spl7_24 | ~spl7_11),
% 1.59/0.62    inference(avatar_split_clause,[],[f220,f160,f227])).
% 1.59/0.62  fof(f220,plain,(
% 1.59/0.62    v1_relat_1(sK5) | ~spl7_11),
% 1.59/0.62    inference(resolution,[],[f95,f162])).
% 1.59/0.62  fof(f95,plain,(
% 1.59/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f48])).
% 1.59/0.62  fof(f48,plain,(
% 1.59/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.62    inference(ennf_transformation,[],[f15])).
% 1.59/0.62  fof(f15,axiom,(
% 1.59/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.59/0.62  fof(f225,plain,(
% 1.59/0.62    spl7_23 | ~spl7_8),
% 1.59/0.62    inference(avatar_split_clause,[],[f219,f145,f222])).
% 1.59/0.62  fof(f219,plain,(
% 1.59/0.62    v1_relat_1(sK4) | ~spl7_8),
% 1.59/0.62    inference(resolution,[],[f95,f147])).
% 1.59/0.62  fof(f196,plain,(
% 1.59/0.62    spl7_18),
% 1.59/0.62    inference(avatar_split_clause,[],[f68,f193])).
% 1.59/0.62  fof(f68,plain,(
% 1.59/0.62    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.59/0.62    inference(cnf_transformation,[],[f11])).
% 1.59/0.62  fof(f11,axiom,(
% 1.59/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.59/0.62  fof(f191,plain,(
% 1.59/0.62    spl7_17),
% 1.59/0.62    inference(avatar_split_clause,[],[f69,f188])).
% 1.59/0.62  fof(f69,plain,(
% 1.59/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.59/0.62    inference(cnf_transformation,[],[f11])).
% 1.59/0.62  fof(f186,plain,(
% 1.59/0.62    ~spl7_14 | ~spl7_15 | ~spl7_16),
% 1.59/0.62    inference(avatar_split_clause,[],[f54,f183,f179,f175])).
% 1.59/0.62  fof(f54,plain,(
% 1.59/0.62    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.59/0.62    inference(cnf_transformation,[],[f28])).
% 1.59/0.62  fof(f28,plain,(
% 1.59/0.62    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.59/0.62    inference(flattening,[],[f27])).
% 1.59/0.62  fof(f27,plain,(
% 1.59/0.62    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.59/0.62    inference(ennf_transformation,[],[f24])).
% 1.59/0.62  fof(f24,negated_conjecture,(
% 1.59/0.62    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.59/0.62    inference(negated_conjecture,[],[f23])).
% 1.59/0.62  fof(f23,conjecture,(
% 1.59/0.62    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).
% 1.59/0.62  fof(f173,plain,(
% 1.59/0.62    spl7_13),
% 1.59/0.62    inference(avatar_split_clause,[],[f55,f170])).
% 1.59/0.62  fof(f55,plain,(
% 1.59/0.62    v1_funct_1(sK5)),
% 1.59/0.62    inference(cnf_transformation,[],[f28])).
% 1.59/0.62  fof(f168,plain,(
% 1.59/0.62    spl7_12),
% 1.59/0.62    inference(avatar_split_clause,[],[f56,f165])).
% 1.59/0.62  fof(f56,plain,(
% 1.59/0.62    v1_funct_2(sK5,sK3,sK1)),
% 1.59/0.62    inference(cnf_transformation,[],[f28])).
% 2.10/0.62  fof(f163,plain,(
% 2.10/0.62    spl7_11),
% 2.10/0.62    inference(avatar_split_clause,[],[f57,f160])).
% 2.10/0.62  fof(f57,plain,(
% 2.10/0.62    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.10/0.62    inference(cnf_transformation,[],[f28])).
% 2.10/0.62  fof(f158,plain,(
% 2.10/0.62    spl7_10),
% 2.10/0.62    inference(avatar_split_clause,[],[f58,f155])).
% 2.10/0.62  fof(f58,plain,(
% 2.10/0.62    v1_funct_1(sK4)),
% 2.10/0.62    inference(cnf_transformation,[],[f28])).
% 2.10/0.62  fof(f153,plain,(
% 2.10/0.62    spl7_9),
% 2.10/0.62    inference(avatar_split_clause,[],[f59,f150])).
% 2.10/0.62  fof(f59,plain,(
% 2.10/0.62    v1_funct_2(sK4,sK2,sK1)),
% 2.10/0.62    inference(cnf_transformation,[],[f28])).
% 2.10/0.62  fof(f148,plain,(
% 2.10/0.62    spl7_8),
% 2.10/0.62    inference(avatar_split_clause,[],[f60,f145])).
% 2.10/0.62  fof(f60,plain,(
% 2.10/0.62    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.10/0.62    inference(cnf_transformation,[],[f28])).
% 2.10/0.62  fof(f143,plain,(
% 2.10/0.62    ~spl7_7),
% 2.10/0.62    inference(avatar_split_clause,[],[f61,f140])).
% 2.10/0.62  fof(f61,plain,(
% 2.10/0.62    ~v1_xboole_0(sK3)),
% 2.10/0.62    inference(cnf_transformation,[],[f28])).
% 2.10/0.62  fof(f138,plain,(
% 2.10/0.62    spl7_6),
% 2.10/0.62    inference(avatar_split_clause,[],[f62,f135])).
% 2.10/0.62  fof(f62,plain,(
% 2.10/0.62    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.10/0.62    inference(cnf_transformation,[],[f28])).
% 2.10/0.62  fof(f133,plain,(
% 2.10/0.62    spl7_5),
% 2.10/0.62    inference(avatar_split_clause,[],[f63,f130])).
% 2.10/0.62  fof(f63,plain,(
% 2.10/0.62    r1_subset_1(sK2,sK3)),
% 2.10/0.62    inference(cnf_transformation,[],[f28])).
% 2.10/0.62  fof(f128,plain,(
% 2.10/0.62    ~spl7_4),
% 2.10/0.62    inference(avatar_split_clause,[],[f64,f125])).
% 2.10/0.62  fof(f64,plain,(
% 2.10/0.62    ~v1_xboole_0(sK2)),
% 2.10/0.62    inference(cnf_transformation,[],[f28])).
% 2.10/0.62  fof(f123,plain,(
% 2.10/0.62    spl7_3),
% 2.10/0.62    inference(avatar_split_clause,[],[f65,f120])).
% 2.10/0.62  fof(f65,plain,(
% 2.10/0.62    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.10/0.62    inference(cnf_transformation,[],[f28])).
% 2.10/0.62  fof(f118,plain,(
% 2.10/0.62    ~spl7_2),
% 2.10/0.62    inference(avatar_split_clause,[],[f66,f115])).
% 2.10/0.62  fof(f66,plain,(
% 2.10/0.62    ~v1_xboole_0(sK1)),
% 2.10/0.62    inference(cnf_transformation,[],[f28])).
% 2.10/0.62  fof(f113,plain,(
% 2.10/0.62    ~spl7_1),
% 2.10/0.62    inference(avatar_split_clause,[],[f67,f110])).
% 2.10/0.62  fof(f67,plain,(
% 2.10/0.62    ~v1_xboole_0(sK0)),
% 2.10/0.62    inference(cnf_transformation,[],[f28])).
% 2.10/0.62  % SZS output end Proof for theBenchmark
% 2.10/0.62  % (2730)------------------------------
% 2.10/0.62  % (2730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.62  % (2730)Termination reason: Refutation
% 2.10/0.62  
% 2.10/0.62  % (2730)Memory used [KB]: 12025
% 2.10/0.62  % (2730)Time elapsed: 0.206 s
% 2.10/0.62  % (2730)------------------------------
% 2.10/0.62  % (2730)------------------------------
% 2.10/0.63  % (2709)Success in time 0.269 s
%------------------------------------------------------------------------------
