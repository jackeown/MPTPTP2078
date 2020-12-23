%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:29 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  306 ( 683 expanded)
%              Number of leaves         :   75 ( 331 expanded)
%              Depth                    :   14
%              Number of atoms          : 1484 (3196 expanded)
%              Number of equality atoms :  187 ( 475 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1932,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f117,f122,f127,f132,f137,f142,f147,f152,f157,f162,f167,f172,f185,f195,f224,f229,f242,f247,f284,f302,f309,f377,f388,f400,f428,f436,f456,f468,f506,f507,f532,f533,f550,f557,f591,f605,f776,f903,f904,f905,f906,f908,f910,f916,f920,f1033,f1103,f1134,f1171,f1819,f1827,f1929,f1931])).

fof(f1931,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | sK4 != k7_relat_1(sK4,k1_relat_1(sK4))
    | k1_xboole_0 != sK4
    | k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1929,plain,
    ( ~ spl7_91
    | ~ spl7_6
    | spl7_16
    | ~ spl7_36
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_115 ),
    inference(avatar_split_clause,[],[f1928,f1027,f402,f398,f306,f182,f134,f773])).

fof(f773,plain,
    ( spl7_91
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f134,plain,
    ( spl7_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f182,plain,
    ( spl7_16
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f306,plain,
    ( spl7_36
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f398,plain,
    ( spl7_46
  <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f402,plain,
    ( spl7_47
  <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f1027,plain,
    ( spl7_115
  <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_115])])).

fof(f1928,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_6
    | spl7_16
    | ~ spl7_36
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_115 ),
    inference(forward_demodulation,[],[f1927,f1029])).

fof(f1029,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl7_115 ),
    inference(avatar_component_clause,[],[f1027])).

fof(f1927,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ spl7_6
    | spl7_16
    | ~ spl7_36
    | ~ spl7_46
    | ~ spl7_47 ),
    inference(forward_demodulation,[],[f1926,f399])).

fof(f399,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f398])).

fof(f1926,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl7_6
    | spl7_16
    | ~ spl7_36
    | ~ spl7_47 ),
    inference(forward_demodulation,[],[f1925,f308])).

fof(f308,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f306])).

fof(f1925,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl7_6
    | spl7_16
    | ~ spl7_47 ),
    inference(forward_demodulation,[],[f1924,f348])).

fof(f348,plain,
    ( ! [X1] : k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))
    | ~ spl7_6 ),
    inference(resolution,[],[f102,f136])).

fof(f136,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f91,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f1924,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl7_16
    | ~ spl7_47 ),
    inference(forward_demodulation,[],[f184,f403])).

fof(f403,plain,
    ( ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f402])).

fof(f184,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f182])).

fof(f1827,plain,
    ( spl7_14
    | spl7_1
    | ~ spl7_125
    | ~ spl7_121
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
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_91
    | ~ spl7_115
    | ~ spl7_129 ),
    inference(avatar_split_clause,[],[f1826,f1168,f1027,f773,f402,f398,f306,f134,f114,f124,f119,f139,f134,f154,f149,f144,f169,f164,f159,f1100,f1131,f109,f174])).

fof(f174,plain,
    ( spl7_14
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f109,plain,
    ( spl7_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1131,plain,
    ( spl7_125
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_125])])).

fof(f1100,plain,
    ( spl7_121
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_121])])).

fof(f159,plain,
    ( spl7_11
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f164,plain,
    ( spl7_12
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f169,plain,
    ( spl7_13
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f144,plain,
    ( spl7_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f149,plain,
    ( spl7_9
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f154,plain,
    ( spl7_10
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f139,plain,
    ( spl7_7
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f119,plain,
    ( spl7_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f124,plain,
    ( spl7_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f114,plain,
    ( spl7_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1168,plain,
    ( spl7_129
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_129])])).

fof(f1826,plain,
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
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_91
    | ~ spl7_115
    | ~ spl7_129 ),
    inference(trivial_inequality_removal,[],[f1825])).

fof(f1825,plain,
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
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_91
    | ~ spl7_115
    | ~ spl7_129 ),
    inference(forward_demodulation,[],[f1824,f775])).

fof(f775,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_91 ),
    inference(avatar_component_clause,[],[f773])).

fof(f1824,plain,
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
    | ~ spl7_6
    | ~ spl7_36
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_115
    | ~ spl7_129 ),
    inference(forward_demodulation,[],[f1823,f1029])).

fof(f1823,plain,
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
    | ~ spl7_6
    | ~ spl7_36
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_129 ),
    inference(forward_demodulation,[],[f1822,f399])).

fof(f1822,plain,
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
    | ~ spl7_47
    | ~ spl7_129 ),
    inference(forward_demodulation,[],[f1821,f308])).

fof(f1821,plain,
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
    | ~ spl7_47
    | ~ spl7_129 ),
    inference(forward_demodulation,[],[f1820,f348])).

fof(f1820,plain,
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
    | ~ spl7_47
    | ~ spl7_129 ),
    inference(forward_demodulation,[],[f1792,f403])).

fof(f1792,plain,
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
    | ~ spl7_129 ),
    inference(resolution,[],[f1170,f105])).

fof(f105,plain,(
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
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f29])).

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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).

fof(f1170,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl7_129 ),
    inference(avatar_component_clause,[],[f1168])).

fof(f1819,plain,
    ( spl7_15
    | spl7_1
    | ~ spl7_125
    | ~ spl7_121
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
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_91
    | ~ spl7_115
    | ~ spl7_129 ),
    inference(avatar_split_clause,[],[f1818,f1168,f1027,f773,f402,f398,f306,f134,f114,f124,f119,f139,f134,f154,f149,f144,f169,f164,f159,f1100,f1131,f109,f178])).

fof(f178,plain,
    ( spl7_15
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f1818,plain,
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
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_91
    | ~ spl7_115
    | ~ spl7_129 ),
    inference(trivial_inequality_removal,[],[f1817])).

fof(f1817,plain,
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
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_91
    | ~ spl7_115
    | ~ spl7_129 ),
    inference(forward_demodulation,[],[f1816,f775])).

fof(f1816,plain,
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
    | ~ spl7_6
    | ~ spl7_36
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_115
    | ~ spl7_129 ),
    inference(forward_demodulation,[],[f1815,f1029])).

fof(f1815,plain,
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
    | ~ spl7_6
    | ~ spl7_36
    | ~ spl7_46
    | ~ spl7_47
    | ~ spl7_129 ),
    inference(forward_demodulation,[],[f1814,f399])).

fof(f1814,plain,
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
    | ~ spl7_47
    | ~ spl7_129 ),
    inference(forward_demodulation,[],[f1813,f308])).

fof(f1813,plain,
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
    | ~ spl7_47
    | ~ spl7_129 ),
    inference(forward_demodulation,[],[f1812,f348])).

fof(f1812,plain,
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
    | ~ spl7_47
    | ~ spl7_129 ),
    inference(forward_demodulation,[],[f1791,f403])).

fof(f1791,plain,
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
    | ~ spl7_129 ),
    inference(resolution,[],[f1170,f106])).

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
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f1171,plain,
    ( spl7_129
    | ~ spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f1166,f705,f144,f149,f154,f1168])).

fof(f705,plain,
    ( spl7_88
  <=> ! [X1] :
        ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f1166,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl7_8
    | ~ spl7_88 ),
    inference(resolution,[],[f706,f146])).

fof(f146,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f144])).

fof(f706,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) )
    | ~ spl7_88 ),
    inference(avatar_component_clause,[],[f705])).

fof(f1134,plain,
    ( spl7_125
    | ~ spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_84 ),
    inference(avatar_split_clause,[],[f1129,f677,f144,f149,f154,f1131])).

fof(f677,plain,
    ( spl7_84
  <=> ! [X1] :
        ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f1129,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl7_8
    | ~ spl7_84 ),
    inference(resolution,[],[f678,f146])).

fof(f678,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) )
    | ~ spl7_84 ),
    inference(avatar_component_clause,[],[f677])).

fof(f1103,plain,
    ( spl7_121
    | ~ spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_75 ),
    inference(avatar_split_clause,[],[f1098,f622,f144,f149,f154,f1100])).

fof(f622,plain,
    ( spl7_75
  <=> ! [X1] :
        ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f1098,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl7_8
    | ~ spl7_75 ),
    inference(resolution,[],[f623,f146])).

fof(f623,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) )
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f622])).

fof(f1033,plain,
    ( spl7_115
    | ~ spl7_24
    | ~ spl7_70
    | ~ spl7_71
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f1032,f602,f554,f547,f226,f1027])).

fof(f226,plain,
    ( spl7_24
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f547,plain,
    ( spl7_70
  <=> k1_xboole_0 = k7_relat_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f554,plain,
    ( spl7_71
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f602,plain,
    ( spl7_73
  <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f1032,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_70
    | ~ spl7_71
    | ~ spl7_73 ),
    inference(forward_demodulation,[],[f1031,f604])).

fof(f604,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_73 ),
    inference(avatar_component_clause,[],[f602])).

fof(f1031,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_70
    | ~ spl7_71 ),
    inference(forward_demodulation,[],[f1009,f549])).

fof(f549,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f547])).

fof(f1009,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_71 ),
    inference(resolution,[],[f352,f556])).

fof(f556,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl7_71 ),
    inference(avatar_component_clause,[],[f554])).

fof(f352,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k7_relat_1(k7_relat_1(sK5,X3),X2) = k7_relat_1(sK5,X2) )
    | ~ spl7_24 ),
    inference(resolution,[],[f90,f228])).

fof(f228,plain,
    ( v1_relat_1(sK5)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f226])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f920,plain,
    ( ~ spl7_24
    | spl7_63
    | ~ spl7_45 ),
    inference(avatar_split_clause,[],[f918,f391,f494,f226])).

fof(f494,plain,
    ( spl7_63
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f391,plain,
    ( spl7_45
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f918,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK3)
        | ~ v1_relat_1(sK5)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl7_45 ),
    inference(superposition,[],[f76,f393])).

fof(f393,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f391])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f916,plain,
    ( ~ spl7_24
    | spl7_45
    | ~ spl7_34
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f915,f379,f286,f391,f226])).

fof(f286,plain,
    ( spl7_34
  <=> v4_relat_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f379,plain,
    ( spl7_43
  <=> v1_partfun1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f915,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl7_43 ),
    inference(resolution,[],[f381,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f381,plain,
    ( v1_partfun1(sK5,sK3)
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f379])).

fof(f910,plain,
    ( ~ spl7_6
    | ~ spl7_12
    | spl7_7
    | ~ spl7_13
    | spl7_2
    | spl7_88
    | ~ spl7_11
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f896,f466,f159,f705,f114,f169,f139,f164,f134])).

fof(f466,plain,
    ( spl7_58
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
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f896,plain,
    ( ! [X6] :
        ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X6,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,sK2,sK1)
        | v1_xboole_0(sK3)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) )
    | ~ spl7_11
    | ~ spl7_58 ),
    inference(resolution,[],[f161,f467])).

fof(f467,plain,
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
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f466])).

fof(f161,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f159])).

fof(f908,plain,
    ( ~ spl7_6
    | ~ spl7_12
    | spl7_7
    | ~ spl7_13
    | spl7_2
    | spl7_84
    | ~ spl7_11
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f894,f454,f159,f677,f114,f169,f139,f164,f134])).

fof(f454,plain,
    ( spl7_56
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
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f894,plain,
    ( ! [X4] :
        ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,sK2,sK1)
        | v1_xboole_0(sK3)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) )
    | ~ spl7_11
    | ~ spl7_56 ),
    inference(resolution,[],[f161,f455])).

fof(f455,plain,
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
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f454])).

fof(f906,plain,
    ( ~ spl7_6
    | ~ spl7_12
    | spl7_7
    | ~ spl7_13
    | spl7_2
    | spl7_75
    | ~ spl7_11
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f891,f434,f159,f622,f114,f169,f139,f164,f134])).

fof(f434,plain,
    ( spl7_52
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
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f891,plain,
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
    | ~ spl7_52 ),
    inference(resolution,[],[f161,f435])).

fof(f435,plain,
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
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f434])).

fof(f905,plain,
    ( spl7_47
    | ~ spl7_13
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f890,f159,f169,f402])).

fof(f890,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK5)
        | k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0) )
    | ~ spl7_11 ),
    inference(resolution,[],[f161,f94])).

fof(f94,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f904,plain,
    ( spl7_34
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f889,f159,f286])).

fof(f889,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl7_11 ),
    inference(resolution,[],[f161,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f903,plain,
    ( spl7_43
    | ~ spl7_12
    | ~ spl7_13
    | spl7_2
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f887,f159,f114,f169,f164,f379])).

fof(f887,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | ~ spl7_11 ),
    inference(resolution,[],[f161,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f776,plain,
    ( spl7_91
    | ~ spl7_23
    | ~ spl7_64
    | ~ spl7_66
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f771,f602,f517,f503,f221,f773])).

fof(f221,plain,
    ( spl7_23
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f503,plain,
    ( spl7_64
  <=> k1_xboole_0 = k7_relat_1(sK4,sK6(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f517,plain,
    ( spl7_66
  <=> r1_tarski(k1_xboole_0,sK6(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f771,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_23
    | ~ spl7_64
    | ~ spl7_66
    | ~ spl7_73 ),
    inference(forward_demodulation,[],[f770,f604])).

fof(f770,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_23
    | ~ spl7_64
    | ~ spl7_66 ),
    inference(forward_demodulation,[],[f757,f505])).

fof(f505,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK6(sK2))
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f503])).

fof(f757,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k7_relat_1(sK4,sK6(sK2)),k1_xboole_0)
    | ~ spl7_23
    | ~ spl7_66 ),
    inference(resolution,[],[f351,f519])).

fof(f519,plain,
    ( r1_tarski(k1_xboole_0,sK6(sK2))
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f517])).

fof(f351,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK4,X0) = k7_relat_1(k7_relat_1(sK4,X1),X0) )
    | ~ spl7_23 ),
    inference(resolution,[],[f90,f223])).

fof(f223,plain,
    ( v1_relat_1(sK4)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f221])).

fof(f605,plain,
    ( spl7_73
    | ~ spl7_18
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f600,f321,f192,f602])).

fof(f192,plain,
    ( spl7_18
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f321,plain,
    ( spl7_38
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f600,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_18
    | ~ spl7_38 ),
    inference(forward_demodulation,[],[f592,f194])).

fof(f194,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f192])).

fof(f592,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl7_38 ),
    inference(resolution,[],[f322,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f322,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f321])).

fof(f591,plain,
    ( spl7_38
    | ~ spl7_23
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f590,f503,f221,f321])).

fof(f590,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_23
    | ~ spl7_64 ),
    inference(superposition,[],[f571,f505])).

fof(f571,plain,
    ( ! [X4] : v1_relat_1(k7_relat_1(sK4,X4))
    | ~ spl7_23 ),
    inference(superposition,[],[f233,f337])).

fof(f337,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k1_setfam_1(k2_tarski(sK4,k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ spl7_23 ),
    inference(resolution,[],[f99,f223])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))) ) ),
    inference(definition_unfolding,[],[f83,f79])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

fof(f233,plain,
    ( ! [X1] : v1_relat_1(k1_setfam_1(k2_tarski(sK4,X1)))
    | ~ spl7_23 ),
    inference(resolution,[],[f223,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f81,f79])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f557,plain,
    ( spl7_71
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f552,f547,f226,f192,f554])).

fof(f552,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_70 ),
    inference(forward_demodulation,[],[f551,f194])).

fof(f551,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK2)
    | ~ spl7_24
    | ~ spl7_70 ),
    inference(superposition,[],[f249,f549])).

fof(f249,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),X0)
    | ~ spl7_24 ),
    inference(resolution,[],[f228,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f550,plain,
    ( spl7_70
    | ~ spl7_35
    | ~ spl7_63 ),
    inference(avatar_split_clause,[],[f540,f494,f299,f547])).

fof(f299,plain,
    ( spl7_35
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f540,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl7_35
    | ~ spl7_63 ),
    inference(resolution,[],[f495,f301])).

fof(f301,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f299])).

fof(f495,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl7_63 ),
    inference(avatar_component_clause,[],[f494])).

fof(f533,plain,
    ( ~ spl7_50
    | spl7_26
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f407,f385,f239,f421])).

fof(f421,plain,
    ( spl7_50
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f239,plain,
    ( spl7_26
  <=> k1_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f385,plain,
    ( spl7_44
  <=> sK2 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f407,plain,
    ( k1_xboole_0 != sK2
    | spl7_26
    | ~ spl7_44 ),
    inference(superposition,[],[f241,f387])).

fof(f387,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f385])).

fof(f241,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | spl7_26 ),
    inference(avatar_component_clause,[],[f239])).

fof(f532,plain,
    ( spl7_66
    | ~ spl7_18
    | ~ spl7_23
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f531,f503,f221,f192,f517])).

fof(f531,plain,
    ( r1_tarski(k1_xboole_0,sK6(sK2))
    | ~ spl7_18
    | ~ spl7_23
    | ~ spl7_64 ),
    inference(forward_demodulation,[],[f514,f194])).

fof(f514,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK6(sK2))
    | ~ spl7_23
    | ~ spl7_64 ),
    inference(superposition,[],[f231,f505])).

fof(f231,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0)
    | ~ spl7_23 ),
    inference(resolution,[],[f223,f82])).

fof(f507,plain,
    ( k1_xboole_0 != sK4
    | v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK4) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f506,plain,
    ( spl7_50
    | spl7_64
    | ~ spl7_51 ),
    inference(avatar_split_clause,[],[f501,f426,f503,f421])).

fof(f426,plain,
    ( spl7_51
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | k1_xboole_0 = k7_relat_1(sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f501,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK6(sK2))
    | k1_xboole_0 = sK2
    | ~ spl7_51 ),
    inference(resolution,[],[f427,f78])).

fof(f78,plain,(
    ! [X0] :
      ( r1_xboole_0(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r1_xboole_0(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r1_xboole_0(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f427,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f426])).

fof(f468,plain,
    ( spl7_1
    | spl7_4
    | spl7_58
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f461,f119,f466,f124,f109])).

fof(f461,plain,
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
    inference(resolution,[],[f97,f121])).

fof(f121,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f97,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(f456,plain,
    ( spl7_1
    | spl7_4
    | spl7_56
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f449,f119,f454,f124,f109])).

fof(f449,plain,
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
    inference(resolution,[],[f96,f121])).

fof(f96,plain,(
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

fof(f436,plain,
    ( spl7_1
    | spl7_4
    | spl7_52
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f429,f119,f434,f124,f109])).

fof(f429,plain,
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
    inference(resolution,[],[f95,f121])).

fof(f95,plain,(
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

fof(f428,plain,
    ( ~ spl7_23
    | spl7_51
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f408,f385,f426,f221])).

fof(f408,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | ~ v1_relat_1(sK4)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl7_44 ),
    inference(superposition,[],[f76,f387])).

fof(f400,plain,
    ( spl7_46
    | ~ spl7_10
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f395,f144,f154,f398])).

fof(f395,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) )
    | ~ spl7_8 ),
    inference(resolution,[],[f94,f146])).

fof(f388,plain,
    ( ~ spl7_23
    | spl7_44
    | ~ spl7_33
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f383,f374,f281,f385,f221])).

fof(f281,plain,
    ( spl7_33
  <=> v4_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f374,plain,
    ( spl7_42
  <=> v1_partfun1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f383,plain,
    ( ~ v4_relat_1(sK4,sK2)
    | sK2 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl7_42 ),
    inference(resolution,[],[f376,f87])).

fof(f376,plain,
    ( v1_partfun1(sK4,sK2)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f374])).

fof(f377,plain,
    ( spl7_42
    | ~ spl7_9
    | ~ spl7_10
    | spl7_2
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f371,f144,f114,f154,f149,f374])).

fof(f371,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f80,f146])).

fof(f309,plain,
    ( spl7_36
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f304,f299,f306])).

fof(f304,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl7_35 ),
    inference(resolution,[],[f301,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f89,f79])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f302,plain,
    ( spl7_4
    | spl7_35
    | spl7_7
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f297,f129,f139,f299,f124])).

fof(f129,plain,
    ( spl7_5
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f297,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2)
    | ~ spl7_5 ),
    inference(resolution,[],[f85,f131])).

fof(f131,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f284,plain,
    ( spl7_33
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f278,f144,f281])).

fof(f278,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f93,f146])).

fof(f247,plain,
    ( spl7_27
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f232,f221,f244])).

fof(f244,plain,
    ( spl7_27
  <=> sK4 = k7_relat_1(sK4,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f232,plain,
    ( sK4 = k7_relat_1(sK4,k1_relat_1(sK4))
    | ~ spl7_23 ),
    inference(resolution,[],[f223,f73])).

fof(f242,plain,
    ( spl7_25
    | ~ spl7_26
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f230,f221,f239,f235])).

fof(f235,plain,
    ( spl7_25
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f230,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | k1_xboole_0 = sK4
    | ~ spl7_23 ),
    inference(resolution,[],[f223,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f229,plain,
    ( spl7_24
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f219,f159,f226])).

fof(f219,plain,
    ( v1_relat_1(sK5)
    | ~ spl7_11 ),
    inference(resolution,[],[f92,f161])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f224,plain,
    ( spl7_23
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f218,f144,f221])).

fof(f218,plain,
    ( v1_relat_1(sK4)
    | ~ spl7_8 ),
    inference(resolution,[],[f92,f146])).

fof(f195,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f68,f192])).

fof(f68,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f185,plain,
    ( ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f54,f182,f178,f174])).

fof(f54,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).

fof(f172,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f55,f169])).

fof(f55,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f167,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f56,f164])).

fof(f56,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f162,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f57,f159])).

fof(f57,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f157,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f58,f154])).

fof(f58,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f152,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f59,f149])).

fof(f59,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f147,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f60,f144])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f142,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f61,f139])).

fof(f61,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f137,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f62,f134])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f132,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f63,f129])).

fof(f63,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f127,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f64,f124])).

fof(f64,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f122,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f65,f119])).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f117,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f66,f114])).

fof(f66,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f112,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f67,f109])).

fof(f67,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 13:51:55 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.48  % (4857)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.49  % (4873)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (4853)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (4852)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (4865)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (4849)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (4871)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (4863)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (4861)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (4854)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (4877)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (4851)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (4850)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (4876)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (4856)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (4872)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (4855)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (4859)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (4858)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (4878)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (4870)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (4869)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (4875)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (4868)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (4874)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.52/0.57  % (4862)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.52/0.57  % (4867)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.52/0.57  % (4860)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.52/0.57  % (4866)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.52/0.57  % (4864)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.52/0.57  % (4866)Refutation not found, incomplete strategy% (4866)------------------------------
% 1.52/0.57  % (4866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (4866)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (4866)Memory used [KB]: 10746
% 1.52/0.57  % (4866)Time elapsed: 0.150 s
% 1.52/0.57  % (4866)------------------------------
% 1.52/0.57  % (4866)------------------------------
% 1.52/0.58  % (4871)Refutation not found, incomplete strategy% (4871)------------------------------
% 1.52/0.58  % (4871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (4871)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.59  
% 1.64/0.59  % (4871)Memory used [KB]: 11513
% 1.64/0.59  % (4871)Time elapsed: 0.108 s
% 1.64/0.59  % (4871)------------------------------
% 1.64/0.59  % (4871)------------------------------
% 1.64/0.62  % (4859)Refutation not found, incomplete strategy% (4859)------------------------------
% 1.64/0.62  % (4859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.62  % (4859)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.62  
% 1.64/0.62  % (4859)Memory used [KB]: 11513
% 1.64/0.62  % (4859)Time elapsed: 0.198 s
% 1.64/0.62  % (4859)------------------------------
% 1.64/0.62  % (4859)------------------------------
% 2.04/0.66  % (4865)Refutation found. Thanks to Tanya!
% 2.04/0.66  % SZS status Theorem for theBenchmark
% 2.04/0.66  % SZS output start Proof for theBenchmark
% 2.04/0.67  fof(f1932,plain,(
% 2.04/0.67    $false),
% 2.04/0.67    inference(avatar_sat_refutation,[],[f112,f117,f122,f127,f132,f137,f142,f147,f152,f157,f162,f167,f172,f185,f195,f224,f229,f242,f247,f284,f302,f309,f377,f388,f400,f428,f436,f456,f468,f506,f507,f532,f533,f550,f557,f591,f605,f776,f903,f904,f905,f906,f908,f910,f916,f920,f1033,f1103,f1134,f1171,f1819,f1827,f1929,f1931])).
% 2.04/0.67  fof(f1931,plain,(
% 2.04/0.67    k1_xboole_0 != k1_relat_1(k1_xboole_0) | sK4 != k7_relat_1(sK4,k1_relat_1(sK4)) | k1_xboole_0 != sK4 | k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 2.04/0.67    introduced(theory_tautology_sat_conflict,[])).
% 2.04/0.67  fof(f1929,plain,(
% 2.04/0.67    ~spl7_91 | ~spl7_6 | spl7_16 | ~spl7_36 | ~spl7_46 | ~spl7_47 | ~spl7_115),
% 2.04/0.67    inference(avatar_split_clause,[],[f1928,f1027,f402,f398,f306,f182,f134,f773])).
% 2.04/0.67  fof(f773,plain,(
% 2.04/0.67    spl7_91 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).
% 2.04/0.67  fof(f134,plain,(
% 2.04/0.67    spl7_6 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 2.04/0.67  fof(f182,plain,(
% 2.04/0.67    spl7_16 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 2.04/0.67  fof(f306,plain,(
% 2.04/0.67    spl7_36 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 2.04/0.67  fof(f398,plain,(
% 2.04/0.67    spl7_46 <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 2.04/0.67  fof(f402,plain,(
% 2.04/0.67    spl7_47 <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 2.04/0.67  fof(f1027,plain,(
% 2.04/0.67    spl7_115 <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_115])])).
% 2.04/0.67  fof(f1928,plain,(
% 2.04/0.67    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | (~spl7_6 | spl7_16 | ~spl7_36 | ~spl7_46 | ~spl7_47 | ~spl7_115)),
% 2.04/0.67    inference(forward_demodulation,[],[f1927,f1029])).
% 2.04/0.67  fof(f1029,plain,(
% 2.04/0.67    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | ~spl7_115),
% 2.04/0.67    inference(avatar_component_clause,[],[f1027])).
% 2.04/0.67  fof(f1927,plain,(
% 2.04/0.67    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | (~spl7_6 | spl7_16 | ~spl7_36 | ~spl7_46 | ~spl7_47)),
% 2.04/0.67    inference(forward_demodulation,[],[f1926,f399])).
% 2.04/0.67  fof(f399,plain,(
% 2.04/0.67    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl7_46),
% 2.04/0.67    inference(avatar_component_clause,[],[f398])).
% 2.04/0.67  fof(f1926,plain,(
% 2.04/0.67    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (~spl7_6 | spl7_16 | ~spl7_36 | ~spl7_47)),
% 2.04/0.67    inference(forward_demodulation,[],[f1925,f308])).
% 2.04/0.67  fof(f308,plain,(
% 2.04/0.67    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl7_36),
% 2.04/0.67    inference(avatar_component_clause,[],[f306])).
% 2.04/0.67  fof(f1925,plain,(
% 2.04/0.67    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | (~spl7_6 | spl7_16 | ~spl7_47)),
% 2.04/0.67    inference(forward_demodulation,[],[f1924,f348])).
% 2.04/0.67  fof(f348,plain,(
% 2.04/0.67    ( ! [X1] : (k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))) ) | ~spl7_6),
% 2.04/0.67    inference(resolution,[],[f102,f136])).
% 2.04/0.67  fof(f136,plain,(
% 2.04/0.67    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl7_6),
% 2.04/0.67    inference(avatar_component_clause,[],[f134])).
% 2.04/0.67  fof(f102,plain,(
% 2.04/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 2.04/0.67    inference(definition_unfolding,[],[f91,f79])).
% 2.04/0.67  fof(f79,plain,(
% 2.04/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.04/0.67    inference(cnf_transformation,[],[f4])).
% 2.04/0.67  fof(f4,axiom,(
% 2.04/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.04/0.67  fof(f91,plain,(
% 2.04/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f47])).
% 2.04/0.67  fof(f47,plain,(
% 2.04/0.67    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.04/0.67    inference(ennf_transformation,[],[f2])).
% 2.04/0.67  fof(f2,axiom,(
% 2.04/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.04/0.67  fof(f1924,plain,(
% 2.04/0.67    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (spl7_16 | ~spl7_47)),
% 2.04/0.67    inference(forward_demodulation,[],[f184,f403])).
% 2.04/0.67  fof(f403,plain,(
% 2.04/0.67    ( ! [X1] : (k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl7_47),
% 2.04/0.67    inference(avatar_component_clause,[],[f402])).
% 2.04/0.67  fof(f184,plain,(
% 2.04/0.67    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl7_16),
% 2.04/0.67    inference(avatar_component_clause,[],[f182])).
% 2.04/0.67  fof(f1827,plain,(
% 2.04/0.67    spl7_14 | spl7_1 | ~spl7_125 | ~spl7_121 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_6 | spl7_7 | ~spl7_3 | spl7_4 | spl7_2 | ~spl7_6 | ~spl7_36 | ~spl7_46 | ~spl7_47 | ~spl7_91 | ~spl7_115 | ~spl7_129),
% 2.04/0.67    inference(avatar_split_clause,[],[f1826,f1168,f1027,f773,f402,f398,f306,f134,f114,f124,f119,f139,f134,f154,f149,f144,f169,f164,f159,f1100,f1131,f109,f174])).
% 2.04/0.67  fof(f174,plain,(
% 2.04/0.67    spl7_14 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 2.04/0.67  fof(f109,plain,(
% 2.04/0.67    spl7_1 <=> v1_xboole_0(sK0)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.04/0.67  fof(f1131,plain,(
% 2.04/0.67    spl7_125 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_125])])).
% 2.04/0.67  fof(f1100,plain,(
% 2.04/0.67    spl7_121 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_121])])).
% 2.04/0.67  fof(f159,plain,(
% 2.04/0.67    spl7_11 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 2.04/0.67  fof(f164,plain,(
% 2.04/0.67    spl7_12 <=> v1_funct_2(sK5,sK3,sK1)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 2.04/0.67  fof(f169,plain,(
% 2.04/0.67    spl7_13 <=> v1_funct_1(sK5)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 2.04/0.67  fof(f144,plain,(
% 2.04/0.67    spl7_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 2.04/0.67  fof(f149,plain,(
% 2.04/0.67    spl7_9 <=> v1_funct_2(sK4,sK2,sK1)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 2.04/0.67  fof(f154,plain,(
% 2.04/0.67    spl7_10 <=> v1_funct_1(sK4)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 2.04/0.67  fof(f139,plain,(
% 2.04/0.67    spl7_7 <=> v1_xboole_0(sK3)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 2.04/0.67  fof(f119,plain,(
% 2.04/0.67    spl7_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.04/0.67  fof(f124,plain,(
% 2.04/0.67    spl7_4 <=> v1_xboole_0(sK2)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.04/0.67  fof(f114,plain,(
% 2.04/0.67    spl7_2 <=> v1_xboole_0(sK1)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.04/0.67  fof(f1168,plain,(
% 2.04/0.67    spl7_129 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_129])])).
% 2.04/0.67  fof(f1826,plain,(
% 2.04/0.67    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_36 | ~spl7_46 | ~spl7_47 | ~spl7_91 | ~spl7_115 | ~spl7_129)),
% 2.04/0.67    inference(trivial_inequality_removal,[],[f1825])).
% 2.04/0.67  fof(f1825,plain,(
% 2.04/0.67    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_36 | ~spl7_46 | ~spl7_47 | ~spl7_91 | ~spl7_115 | ~spl7_129)),
% 2.04/0.67    inference(forward_demodulation,[],[f1824,f775])).
% 2.04/0.67  fof(f775,plain,(
% 2.04/0.67    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl7_91),
% 2.04/0.67    inference(avatar_component_clause,[],[f773])).
% 2.04/0.67  fof(f1824,plain,(
% 2.04/0.67    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_36 | ~spl7_46 | ~spl7_47 | ~spl7_115 | ~spl7_129)),
% 2.04/0.67    inference(forward_demodulation,[],[f1823,f1029])).
% 2.04/0.67  fof(f1823,plain,(
% 2.04/0.67    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_36 | ~spl7_46 | ~spl7_47 | ~spl7_129)),
% 2.04/0.67    inference(forward_demodulation,[],[f1822,f399])).
% 2.04/0.67  fof(f1822,plain,(
% 2.04/0.67    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_36 | ~spl7_47 | ~spl7_129)),
% 2.04/0.67    inference(forward_demodulation,[],[f1821,f308])).
% 2.04/0.67  fof(f1821,plain,(
% 2.04/0.67    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_47 | ~spl7_129)),
% 2.04/0.67    inference(forward_demodulation,[],[f1820,f348])).
% 2.04/0.67  fof(f1820,plain,(
% 2.04/0.67    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_47 | ~spl7_129)),
% 2.04/0.67    inference(forward_demodulation,[],[f1792,f403])).
% 2.04/0.67  fof(f1792,plain,(
% 2.04/0.67    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~spl7_129),
% 2.04/0.67    inference(resolution,[],[f1170,f105])).
% 2.04/0.67  fof(f105,plain,(
% 2.04/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 2.04/0.67    inference(equality_resolution,[],[f71])).
% 2.04/0.67  fof(f71,plain,(
% 2.04/0.67    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 2.04/0.67    inference(cnf_transformation,[],[f29])).
% 2.04/0.67  fof(f29,plain,(
% 2.04/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.04/0.67    inference(flattening,[],[f28])).
% 2.04/0.67  fof(f28,plain,(
% 2.04/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.04/0.67    inference(ennf_transformation,[],[f20])).
% 2.04/0.67  fof(f20,axiom,(
% 2.04/0.67    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 2.04/0.67  fof(f1170,plain,(
% 2.04/0.67    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl7_129),
% 2.04/0.67    inference(avatar_component_clause,[],[f1168])).
% 2.04/0.67  fof(f1819,plain,(
% 2.04/0.67    spl7_15 | spl7_1 | ~spl7_125 | ~spl7_121 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_6 | spl7_7 | ~spl7_3 | spl7_4 | spl7_2 | ~spl7_6 | ~spl7_36 | ~spl7_46 | ~spl7_47 | ~spl7_91 | ~spl7_115 | ~spl7_129),
% 2.04/0.67    inference(avatar_split_clause,[],[f1818,f1168,f1027,f773,f402,f398,f306,f134,f114,f124,f119,f139,f134,f154,f149,f144,f169,f164,f159,f1100,f1131,f109,f178])).
% 2.04/0.67  fof(f178,plain,(
% 2.04/0.67    spl7_15 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 2.04/0.67  fof(f1818,plain,(
% 2.04/0.67    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_36 | ~spl7_46 | ~spl7_47 | ~spl7_91 | ~spl7_115 | ~spl7_129)),
% 2.04/0.67    inference(trivial_inequality_removal,[],[f1817])).
% 2.04/0.67  fof(f1817,plain,(
% 2.04/0.67    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_36 | ~spl7_46 | ~spl7_47 | ~spl7_91 | ~spl7_115 | ~spl7_129)),
% 2.04/0.67    inference(forward_demodulation,[],[f1816,f775])).
% 2.04/0.67  fof(f1816,plain,(
% 2.04/0.67    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_36 | ~spl7_46 | ~spl7_47 | ~spl7_115 | ~spl7_129)),
% 2.04/0.67    inference(forward_demodulation,[],[f1815,f1029])).
% 2.04/0.67  fof(f1815,plain,(
% 2.04/0.67    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_36 | ~spl7_46 | ~spl7_47 | ~spl7_129)),
% 2.04/0.67    inference(forward_demodulation,[],[f1814,f399])).
% 2.04/0.67  fof(f1814,plain,(
% 2.04/0.67    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_36 | ~spl7_47 | ~spl7_129)),
% 2.04/0.67    inference(forward_demodulation,[],[f1813,f308])).
% 2.04/0.67  fof(f1813,plain,(
% 2.04/0.67    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_47 | ~spl7_129)),
% 2.04/0.67    inference(forward_demodulation,[],[f1812,f348])).
% 2.04/0.67  fof(f1812,plain,(
% 2.04/0.67    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_47 | ~spl7_129)),
% 2.04/0.67    inference(forward_demodulation,[],[f1791,f403])).
% 2.04/0.67  fof(f1791,plain,(
% 2.04/0.67    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~spl7_129),
% 2.04/0.67    inference(resolution,[],[f1170,f106])).
% 2.04/0.67  fof(f106,plain,(
% 2.04/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 2.04/0.67    inference(equality_resolution,[],[f70])).
% 2.04/0.67  fof(f70,plain,(
% 2.04/0.67    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 2.04/0.67    inference(cnf_transformation,[],[f29])).
% 2.04/0.67  fof(f1171,plain,(
% 2.04/0.67    spl7_129 | ~spl7_10 | ~spl7_9 | ~spl7_8 | ~spl7_88),
% 2.04/0.67    inference(avatar_split_clause,[],[f1166,f705,f144,f149,f154,f1168])).
% 2.04/0.67  fof(f705,plain,(
% 2.04/0.67    spl7_88 <=> ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).
% 2.04/0.67  fof(f1166,plain,(
% 2.04/0.67    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl7_8 | ~spl7_88)),
% 2.04/0.67    inference(resolution,[],[f706,f146])).
% 2.04/0.67  fof(f146,plain,(
% 2.04/0.67    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl7_8),
% 2.04/0.67    inference(avatar_component_clause,[],[f144])).
% 2.04/0.67  fof(f706,plain,(
% 2.04/0.67    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))) ) | ~spl7_88),
% 2.04/0.67    inference(avatar_component_clause,[],[f705])).
% 2.04/0.67  fof(f1134,plain,(
% 2.04/0.67    spl7_125 | ~spl7_10 | ~spl7_9 | ~spl7_8 | ~spl7_84),
% 2.04/0.67    inference(avatar_split_clause,[],[f1129,f677,f144,f149,f154,f1131])).
% 2.04/0.67  fof(f677,plain,(
% 2.04/0.67    spl7_84 <=> ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).
% 2.04/0.67  fof(f1129,plain,(
% 2.04/0.67    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl7_8 | ~spl7_84)),
% 2.04/0.67    inference(resolution,[],[f678,f146])).
% 2.04/0.67  fof(f678,plain,(
% 2.04/0.67    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)) ) | ~spl7_84),
% 2.04/0.67    inference(avatar_component_clause,[],[f677])).
% 2.04/0.67  fof(f1103,plain,(
% 2.04/0.67    spl7_121 | ~spl7_10 | ~spl7_9 | ~spl7_8 | ~spl7_75),
% 2.04/0.67    inference(avatar_split_clause,[],[f1098,f622,f144,f149,f154,f1100])).
% 2.04/0.67  fof(f622,plain,(
% 2.04/0.67    spl7_75 <=> ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).
% 2.04/0.67  fof(f1098,plain,(
% 2.04/0.67    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl7_8 | ~spl7_75)),
% 2.04/0.67    inference(resolution,[],[f623,f146])).
% 2.04/0.67  fof(f623,plain,(
% 2.04/0.67    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))) ) | ~spl7_75),
% 2.04/0.67    inference(avatar_component_clause,[],[f622])).
% 2.04/0.67  fof(f1033,plain,(
% 2.04/0.67    spl7_115 | ~spl7_24 | ~spl7_70 | ~spl7_71 | ~spl7_73),
% 2.04/0.67    inference(avatar_split_clause,[],[f1032,f602,f554,f547,f226,f1027])).
% 2.04/0.67  fof(f226,plain,(
% 2.04/0.67    spl7_24 <=> v1_relat_1(sK5)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 2.04/0.67  fof(f547,plain,(
% 2.04/0.67    spl7_70 <=> k1_xboole_0 = k7_relat_1(sK5,sK2)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).
% 2.04/0.67  fof(f554,plain,(
% 2.04/0.67    spl7_71 <=> r1_tarski(k1_xboole_0,sK2)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).
% 2.04/0.67  fof(f602,plain,(
% 2.04/0.67    spl7_73 <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).
% 2.04/0.67  fof(f1032,plain,(
% 2.04/0.67    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | (~spl7_24 | ~spl7_70 | ~spl7_71 | ~spl7_73)),
% 2.04/0.67    inference(forward_demodulation,[],[f1031,f604])).
% 2.04/0.67  fof(f604,plain,(
% 2.04/0.67    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | ~spl7_73),
% 2.04/0.67    inference(avatar_component_clause,[],[f602])).
% 2.04/0.67  fof(f1031,plain,(
% 2.04/0.67    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(sK5,k1_xboole_0) | (~spl7_24 | ~spl7_70 | ~spl7_71)),
% 2.04/0.67    inference(forward_demodulation,[],[f1009,f549])).
% 2.04/0.67  fof(f549,plain,(
% 2.04/0.67    k1_xboole_0 = k7_relat_1(sK5,sK2) | ~spl7_70),
% 2.04/0.67    inference(avatar_component_clause,[],[f547])).
% 2.04/0.67  fof(f1009,plain,(
% 2.04/0.67    k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0) | (~spl7_24 | ~spl7_71)),
% 2.04/0.67    inference(resolution,[],[f352,f556])).
% 2.04/0.67  fof(f556,plain,(
% 2.04/0.67    r1_tarski(k1_xboole_0,sK2) | ~spl7_71),
% 2.04/0.67    inference(avatar_component_clause,[],[f554])).
% 2.04/0.67  fof(f352,plain,(
% 2.04/0.67    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k7_relat_1(k7_relat_1(sK5,X3),X2) = k7_relat_1(sK5,X2)) ) | ~spl7_24),
% 2.04/0.67    inference(resolution,[],[f90,f228])).
% 2.04/0.67  fof(f228,plain,(
% 2.04/0.67    v1_relat_1(sK5) | ~spl7_24),
% 2.04/0.67    inference(avatar_component_clause,[],[f226])).
% 2.04/0.67  fof(f90,plain,(
% 2.04/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f46])).
% 2.04/0.67  fof(f46,plain,(
% 2.04/0.67    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 2.04/0.67    inference(flattening,[],[f45])).
% 2.04/0.67  fof(f45,plain,(
% 2.04/0.67    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 2.04/0.67    inference(ennf_transformation,[],[f6])).
% 2.04/0.67  fof(f6,axiom,(
% 2.04/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 2.04/0.67  fof(f920,plain,(
% 2.04/0.67    ~spl7_24 | spl7_63 | ~spl7_45),
% 2.04/0.67    inference(avatar_split_clause,[],[f918,f391,f494,f226])).
% 2.04/0.67  fof(f494,plain,(
% 2.04/0.67    spl7_63 <=> ! [X0] : (~r1_xboole_0(X0,sK3) | k1_xboole_0 = k7_relat_1(sK5,X0))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).
% 2.04/0.67  fof(f391,plain,(
% 2.04/0.67    spl7_45 <=> sK3 = k1_relat_1(sK5)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 2.04/0.67  fof(f918,plain,(
% 2.04/0.67    ( ! [X0] : (~r1_xboole_0(X0,sK3) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl7_45),
% 2.04/0.67    inference(superposition,[],[f76,f393])).
% 2.04/0.67  fof(f393,plain,(
% 2.04/0.67    sK3 = k1_relat_1(sK5) | ~spl7_45),
% 2.04/0.67    inference(avatar_component_clause,[],[f391])).
% 2.04/0.67  fof(f76,plain,(
% 2.04/0.67    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f33])).
% 2.04/0.67  fof(f33,plain,(
% 2.04/0.67    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.04/0.67    inference(ennf_transformation,[],[f7])).
% 2.04/0.67  fof(f7,axiom,(
% 2.04/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 2.04/0.67  fof(f916,plain,(
% 2.04/0.67    ~spl7_24 | spl7_45 | ~spl7_34 | ~spl7_43),
% 2.04/0.67    inference(avatar_split_clause,[],[f915,f379,f286,f391,f226])).
% 2.04/0.67  fof(f286,plain,(
% 2.04/0.67    spl7_34 <=> v4_relat_1(sK5,sK3)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 2.04/0.67  fof(f379,plain,(
% 2.04/0.67    spl7_43 <=> v1_partfun1(sK5,sK3)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 2.04/0.67  fof(f915,plain,(
% 2.04/0.67    ~v4_relat_1(sK5,sK3) | sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5) | ~spl7_43),
% 2.04/0.67    inference(resolution,[],[f381,f87])).
% 2.04/0.67  fof(f87,plain,(
% 2.04/0.67    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f44])).
% 2.04/0.67  fof(f44,plain,(
% 2.04/0.67    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.04/0.67    inference(flattening,[],[f43])).
% 2.04/0.67  fof(f43,plain,(
% 2.04/0.67    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.04/0.67    inference(ennf_transformation,[],[f18])).
% 2.04/0.67  fof(f18,axiom,(
% 2.04/0.67    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 2.04/0.67  fof(f381,plain,(
% 2.04/0.67    v1_partfun1(sK5,sK3) | ~spl7_43),
% 2.04/0.67    inference(avatar_component_clause,[],[f379])).
% 2.04/0.67  fof(f910,plain,(
% 2.04/0.67    ~spl7_6 | ~spl7_12 | spl7_7 | ~spl7_13 | spl7_2 | spl7_88 | ~spl7_11 | ~spl7_58),
% 2.04/0.67    inference(avatar_split_clause,[],[f896,f466,f159,f705,f114,f169,f139,f164,f134])).
% 2.04/0.67  fof(f466,plain,(
% 2.04/0.67    spl7_58 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).
% 2.04/0.67  fof(f896,plain,(
% 2.04/0.67    ( ! [X6] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X6,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl7_11 | ~spl7_58)),
% 2.04/0.67    inference(resolution,[],[f161,f467])).
% 2.04/0.67  fof(f467,plain,(
% 2.04/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl7_58),
% 2.04/0.67    inference(avatar_component_clause,[],[f466])).
% 2.04/0.67  fof(f161,plain,(
% 2.04/0.67    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl7_11),
% 2.04/0.67    inference(avatar_component_clause,[],[f159])).
% 2.04/0.67  fof(f908,plain,(
% 2.04/0.67    ~spl7_6 | ~spl7_12 | spl7_7 | ~spl7_13 | spl7_2 | spl7_84 | ~spl7_11 | ~spl7_56),
% 2.04/0.67    inference(avatar_split_clause,[],[f894,f454,f159,f677,f114,f169,f139,f164,f134])).
% 2.04/0.67  fof(f454,plain,(
% 2.04/0.67    spl7_56 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 2.04/0.67  fof(f894,plain,(
% 2.04/0.67    ( ! [X4] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl7_11 | ~spl7_56)),
% 2.04/0.67    inference(resolution,[],[f161,f455])).
% 2.04/0.67  fof(f455,plain,(
% 2.04/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl7_56),
% 2.04/0.67    inference(avatar_component_clause,[],[f454])).
% 2.04/0.67  fof(f906,plain,(
% 2.04/0.67    ~spl7_6 | ~spl7_12 | spl7_7 | ~spl7_13 | spl7_2 | spl7_75 | ~spl7_11 | ~spl7_52),
% 2.04/0.67    inference(avatar_split_clause,[],[f891,f434,f159,f622,f114,f169,f139,f164,f134])).
% 2.04/0.67  fof(f434,plain,(
% 2.04/0.67    spl7_52 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 2.04/0.67  fof(f891,plain,(
% 2.04/0.67    ( ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl7_11 | ~spl7_52)),
% 2.04/0.67    inference(resolution,[],[f161,f435])).
% 2.04/0.67  fof(f435,plain,(
% 2.04/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl7_52),
% 2.04/0.67    inference(avatar_component_clause,[],[f434])).
% 2.04/0.67  fof(f905,plain,(
% 2.04/0.67    spl7_47 | ~spl7_13 | ~spl7_11),
% 2.04/0.67    inference(avatar_split_clause,[],[f890,f159,f169,f402])).
% 2.04/0.67  fof(f890,plain,(
% 2.04/0.67    ( ! [X0] : (~v1_funct_1(sK5) | k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0)) ) | ~spl7_11),
% 2.04/0.67    inference(resolution,[],[f161,f94])).
% 2.04/0.67  fof(f94,plain,(
% 2.04/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f51])).
% 2.04/0.67  fof(f51,plain,(
% 2.04/0.67    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.04/0.67    inference(flattening,[],[f50])).
% 2.04/0.67  fof(f50,plain,(
% 2.04/0.67    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.04/0.67    inference(ennf_transformation,[],[f19])).
% 2.04/0.67  fof(f19,axiom,(
% 2.04/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.04/0.67  fof(f904,plain,(
% 2.04/0.67    spl7_34 | ~spl7_11),
% 2.04/0.67    inference(avatar_split_clause,[],[f889,f159,f286])).
% 2.04/0.67  fof(f889,plain,(
% 2.04/0.67    v4_relat_1(sK5,sK3) | ~spl7_11),
% 2.04/0.67    inference(resolution,[],[f161,f93])).
% 2.04/0.67  fof(f93,plain,(
% 2.04/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f49])).
% 2.04/0.67  fof(f49,plain,(
% 2.04/0.67    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/0.67    inference(ennf_transformation,[],[f25])).
% 2.04/0.67  fof(f25,plain,(
% 2.04/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.04/0.67    inference(pure_predicate_removal,[],[f15])).
% 2.04/0.67  fof(f15,axiom,(
% 2.04/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.04/0.67  fof(f903,plain,(
% 2.04/0.67    spl7_43 | ~spl7_12 | ~spl7_13 | spl7_2 | ~spl7_11),
% 2.04/0.67    inference(avatar_split_clause,[],[f887,f159,f114,f169,f164,f379])).
% 2.04/0.67  fof(f887,plain,(
% 2.04/0.67    v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3) | ~spl7_11),
% 2.04/0.67    inference(resolution,[],[f161,f80])).
% 2.04/0.67  fof(f80,plain,(
% 2.04/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f37])).
% 2.04/0.67  fof(f37,plain,(
% 2.04/0.67    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.04/0.67    inference(flattening,[],[f36])).
% 2.04/0.67  fof(f36,plain,(
% 2.04/0.67    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.04/0.67    inference(ennf_transformation,[],[f17])).
% 2.04/0.67  fof(f17,axiom,(
% 2.04/0.67    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 2.04/0.67  fof(f776,plain,(
% 2.04/0.67    spl7_91 | ~spl7_23 | ~spl7_64 | ~spl7_66 | ~spl7_73),
% 2.04/0.67    inference(avatar_split_clause,[],[f771,f602,f517,f503,f221,f773])).
% 2.04/0.67  fof(f221,plain,(
% 2.04/0.67    spl7_23 <=> v1_relat_1(sK4)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 2.04/0.67  fof(f503,plain,(
% 2.04/0.67    spl7_64 <=> k1_xboole_0 = k7_relat_1(sK4,sK6(sK2))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).
% 2.04/0.67  fof(f517,plain,(
% 2.04/0.67    spl7_66 <=> r1_tarski(k1_xboole_0,sK6(sK2))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).
% 2.04/0.67  fof(f771,plain,(
% 2.04/0.67    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | (~spl7_23 | ~spl7_64 | ~spl7_66 | ~spl7_73)),
% 2.04/0.67    inference(forward_demodulation,[],[f770,f604])).
% 2.04/0.67  fof(f770,plain,(
% 2.04/0.67    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0) | (~spl7_23 | ~spl7_64 | ~spl7_66)),
% 2.04/0.67    inference(forward_demodulation,[],[f757,f505])).
% 2.04/0.67  fof(f505,plain,(
% 2.04/0.67    k1_xboole_0 = k7_relat_1(sK4,sK6(sK2)) | ~spl7_64),
% 2.04/0.67    inference(avatar_component_clause,[],[f503])).
% 2.04/0.67  fof(f757,plain,(
% 2.04/0.67    k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k7_relat_1(sK4,sK6(sK2)),k1_xboole_0) | (~spl7_23 | ~spl7_66)),
% 2.04/0.67    inference(resolution,[],[f351,f519])).
% 2.04/0.67  fof(f519,plain,(
% 2.04/0.67    r1_tarski(k1_xboole_0,sK6(sK2)) | ~spl7_66),
% 2.04/0.67    inference(avatar_component_clause,[],[f517])).
% 2.04/0.67  fof(f351,plain,(
% 2.04/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(sK4,X0) = k7_relat_1(k7_relat_1(sK4,X1),X0)) ) | ~spl7_23),
% 2.04/0.67    inference(resolution,[],[f90,f223])).
% 2.04/0.67  fof(f223,plain,(
% 2.04/0.67    v1_relat_1(sK4) | ~spl7_23),
% 2.04/0.67    inference(avatar_component_clause,[],[f221])).
% 2.04/0.67  fof(f605,plain,(
% 2.04/0.67    spl7_73 | ~spl7_18 | ~spl7_38),
% 2.04/0.67    inference(avatar_split_clause,[],[f600,f321,f192,f602])).
% 2.04/0.67  fof(f192,plain,(
% 2.04/0.67    spl7_18 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 2.04/0.67  fof(f321,plain,(
% 2.04/0.67    spl7_38 <=> v1_relat_1(k1_xboole_0)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 2.04/0.67  fof(f600,plain,(
% 2.04/0.67    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | (~spl7_18 | ~spl7_38)),
% 2.04/0.67    inference(forward_demodulation,[],[f592,f194])).
% 2.04/0.67  fof(f194,plain,(
% 2.04/0.67    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_18),
% 2.04/0.67    inference(avatar_component_clause,[],[f192])).
% 2.04/0.67  fof(f592,plain,(
% 2.04/0.67    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) | ~spl7_38),
% 2.04/0.67    inference(resolution,[],[f322,f73])).
% 2.04/0.67  fof(f73,plain,(
% 2.04/0.67    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 2.04/0.67    inference(cnf_transformation,[],[f30])).
% 2.04/0.67  fof(f30,plain,(
% 2.04/0.67    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.04/0.67    inference(ennf_transformation,[],[f12])).
% 2.04/0.67  fof(f12,axiom,(
% 2.04/0.67    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 2.04/0.67  fof(f322,plain,(
% 2.04/0.67    v1_relat_1(k1_xboole_0) | ~spl7_38),
% 2.04/0.67    inference(avatar_component_clause,[],[f321])).
% 2.04/0.67  fof(f591,plain,(
% 2.04/0.67    spl7_38 | ~spl7_23 | ~spl7_64),
% 2.04/0.67    inference(avatar_split_clause,[],[f590,f503,f221,f321])).
% 2.04/0.67  fof(f590,plain,(
% 2.04/0.67    v1_relat_1(k1_xboole_0) | (~spl7_23 | ~spl7_64)),
% 2.04/0.67    inference(superposition,[],[f571,f505])).
% 2.04/0.67  fof(f571,plain,(
% 2.04/0.67    ( ! [X4] : (v1_relat_1(k7_relat_1(sK4,X4))) ) | ~spl7_23),
% 2.04/0.67    inference(superposition,[],[f233,f337])).
% 2.04/0.67  fof(f337,plain,(
% 2.04/0.67    ( ! [X0] : (k7_relat_1(sK4,X0) = k1_setfam_1(k2_tarski(sK4,k2_zfmisc_1(X0,k2_relat_1(sK4))))) ) | ~spl7_23),
% 2.04/0.67    inference(resolution,[],[f99,f223])).
% 2.04/0.67  fof(f99,plain,(
% 2.04/0.67    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(X0,k2_relat_1(X1))))) )),
% 2.04/0.67    inference(definition_unfolding,[],[f83,f79])).
% 2.04/0.67  fof(f83,plain,(
% 2.04/0.67    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))) )),
% 2.04/0.67    inference(cnf_transformation,[],[f40])).
% 2.04/0.67  fof(f40,plain,(
% 2.04/0.67    ! [X0,X1] : (k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.04/0.67    inference(ennf_transformation,[],[f11])).
% 2.04/0.67  fof(f11,axiom,(
% 2.04/0.67    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).
% 2.04/0.67  fof(f233,plain,(
% 2.04/0.67    ( ! [X1] : (v1_relat_1(k1_setfam_1(k2_tarski(sK4,X1)))) ) | ~spl7_23),
% 2.04/0.67    inference(resolution,[],[f223,f98])).
% 2.04/0.67  fof(f98,plain,(
% 2.04/0.67    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.04/0.67    inference(definition_unfolding,[],[f81,f79])).
% 2.04/0.67  fof(f81,plain,(
% 2.04/0.67    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1))) )),
% 2.04/0.67    inference(cnf_transformation,[],[f38])).
% 2.04/0.67  fof(f38,plain,(
% 2.04/0.67    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 2.04/0.67    inference(ennf_transformation,[],[f5])).
% 2.04/0.67  fof(f5,axiom,(
% 2.04/0.67    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 2.04/0.67  fof(f557,plain,(
% 2.04/0.67    spl7_71 | ~spl7_18 | ~spl7_24 | ~spl7_70),
% 2.04/0.67    inference(avatar_split_clause,[],[f552,f547,f226,f192,f554])).
% 2.04/0.67  fof(f552,plain,(
% 2.04/0.67    r1_tarski(k1_xboole_0,sK2) | (~spl7_18 | ~spl7_24 | ~spl7_70)),
% 2.04/0.67    inference(forward_demodulation,[],[f551,f194])).
% 2.04/0.67  fof(f551,plain,(
% 2.04/0.67    r1_tarski(k1_relat_1(k1_xboole_0),sK2) | (~spl7_24 | ~spl7_70)),
% 2.04/0.67    inference(superposition,[],[f249,f549])).
% 2.04/0.67  fof(f249,plain,(
% 2.04/0.67    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),X0)) ) | ~spl7_24),
% 2.04/0.67    inference(resolution,[],[f228,f82])).
% 2.04/0.67  fof(f82,plain,(
% 2.04/0.67    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f39])).
% 2.04/0.67  fof(f39,plain,(
% 2.04/0.67    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.04/0.67    inference(ennf_transformation,[],[f10])).
% 2.04/0.67  fof(f10,axiom,(
% 2.04/0.67    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 2.04/0.67  fof(f550,plain,(
% 2.04/0.67    spl7_70 | ~spl7_35 | ~spl7_63),
% 2.04/0.67    inference(avatar_split_clause,[],[f540,f494,f299,f547])).
% 2.04/0.67  fof(f299,plain,(
% 2.04/0.67    spl7_35 <=> r1_xboole_0(sK2,sK3)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 2.04/0.67  fof(f540,plain,(
% 2.04/0.67    k1_xboole_0 = k7_relat_1(sK5,sK2) | (~spl7_35 | ~spl7_63)),
% 2.04/0.67    inference(resolution,[],[f495,f301])).
% 2.04/0.67  fof(f301,plain,(
% 2.04/0.67    r1_xboole_0(sK2,sK3) | ~spl7_35),
% 2.04/0.67    inference(avatar_component_clause,[],[f299])).
% 2.04/0.67  fof(f495,plain,(
% 2.04/0.67    ( ! [X0] : (~r1_xboole_0(X0,sK3) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl7_63),
% 2.04/0.67    inference(avatar_component_clause,[],[f494])).
% 2.04/0.67  fof(f533,plain,(
% 2.04/0.67    ~spl7_50 | spl7_26 | ~spl7_44),
% 2.04/0.67    inference(avatar_split_clause,[],[f407,f385,f239,f421])).
% 2.04/0.67  fof(f421,plain,(
% 2.04/0.67    spl7_50 <=> k1_xboole_0 = sK2),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 2.04/0.67  fof(f239,plain,(
% 2.04/0.67    spl7_26 <=> k1_xboole_0 = k1_relat_1(sK4)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 2.04/0.67  fof(f385,plain,(
% 2.04/0.67    spl7_44 <=> sK2 = k1_relat_1(sK4)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 2.04/0.67  fof(f407,plain,(
% 2.04/0.67    k1_xboole_0 != sK2 | (spl7_26 | ~spl7_44)),
% 2.04/0.67    inference(superposition,[],[f241,f387])).
% 2.04/0.67  fof(f387,plain,(
% 2.04/0.67    sK2 = k1_relat_1(sK4) | ~spl7_44),
% 2.04/0.67    inference(avatar_component_clause,[],[f385])).
% 2.04/0.67  fof(f241,plain,(
% 2.04/0.67    k1_xboole_0 != k1_relat_1(sK4) | spl7_26),
% 2.04/0.67    inference(avatar_component_clause,[],[f239])).
% 2.04/0.67  fof(f532,plain,(
% 2.04/0.67    spl7_66 | ~spl7_18 | ~spl7_23 | ~spl7_64),
% 2.04/0.67    inference(avatar_split_clause,[],[f531,f503,f221,f192,f517])).
% 2.04/0.67  fof(f531,plain,(
% 2.04/0.67    r1_tarski(k1_xboole_0,sK6(sK2)) | (~spl7_18 | ~spl7_23 | ~spl7_64)),
% 2.04/0.67    inference(forward_demodulation,[],[f514,f194])).
% 2.04/0.67  fof(f514,plain,(
% 2.04/0.67    r1_tarski(k1_relat_1(k1_xboole_0),sK6(sK2)) | (~spl7_23 | ~spl7_64)),
% 2.04/0.67    inference(superposition,[],[f231,f505])).
% 2.04/0.67  fof(f231,plain,(
% 2.04/0.67    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0)) ) | ~spl7_23),
% 2.04/0.67    inference(resolution,[],[f223,f82])).
% 2.04/0.67  fof(f507,plain,(
% 2.04/0.67    k1_xboole_0 != sK4 | v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK4)),
% 2.04/0.67    introduced(theory_tautology_sat_conflict,[])).
% 2.04/0.67  fof(f506,plain,(
% 2.04/0.67    spl7_50 | spl7_64 | ~spl7_51),
% 2.04/0.67    inference(avatar_split_clause,[],[f501,f426,f503,f421])).
% 2.04/0.67  fof(f426,plain,(
% 2.04/0.67    spl7_51 <=> ! [X0] : (~r1_xboole_0(X0,sK2) | k1_xboole_0 = k7_relat_1(sK4,X0))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).
% 2.04/0.67  fof(f501,plain,(
% 2.04/0.67    k1_xboole_0 = k7_relat_1(sK4,sK6(sK2)) | k1_xboole_0 = sK2 | ~spl7_51),
% 2.04/0.67    inference(resolution,[],[f427,f78])).
% 2.04/0.67  fof(f78,plain,(
% 2.04/0.67    ( ! [X0] : (r1_xboole_0(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 2.04/0.67    inference(cnf_transformation,[],[f35])).
% 2.04/0.67  fof(f35,plain,(
% 2.04/0.67    ! [X0] : (? [X1] : r1_xboole_0(X1,X0) | k1_xboole_0 = X0)),
% 2.04/0.67    inference(ennf_transformation,[],[f24])).
% 2.04/0.67  fof(f24,plain,(
% 2.04/0.67    ! [X0] : ~(! [X1] : ~r1_xboole_0(X1,X0) & k1_xboole_0 != X0)),
% 2.04/0.67    inference(pure_predicate_removal,[],[f16])).
% 2.04/0.67  fof(f16,axiom,(
% 2.04/0.67    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 2.04/0.67  fof(f427,plain,(
% 2.04/0.67    ( ! [X0] : (~r1_xboole_0(X0,sK2) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl7_51),
% 2.04/0.67    inference(avatar_component_clause,[],[f426])).
% 2.04/0.67  fof(f468,plain,(
% 2.04/0.67    spl7_1 | spl7_4 | spl7_58 | ~spl7_3),
% 2.04/0.67    inference(avatar_split_clause,[],[f461,f119,f466,f124,f109])).
% 2.04/0.67  fof(f461,plain,(
% 2.04/0.67    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0)))) ) | ~spl7_3),
% 2.04/0.67    inference(resolution,[],[f97,f121])).
% 2.04/0.67  fof(f121,plain,(
% 2.04/0.67    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl7_3),
% 2.04/0.67    inference(avatar_component_clause,[],[f119])).
% 2.04/0.67  fof(f97,plain,(
% 2.04/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 2.04/0.67    inference(cnf_transformation,[],[f53])).
% 2.04/0.67  fof(f53,plain,(
% 2.04/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.04/0.67    inference(flattening,[],[f52])).
% 2.04/0.67  fof(f52,plain,(
% 2.04/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.04/0.67    inference(ennf_transformation,[],[f21])).
% 2.04/0.67  fof(f21,axiom,(
% 2.04/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 2.04/0.67  fof(f456,plain,(
% 2.04/0.67    spl7_1 | spl7_4 | spl7_56 | ~spl7_3),
% 2.04/0.67    inference(avatar_split_clause,[],[f449,f119,f454,f124,f109])).
% 2.04/0.67  fof(f449,plain,(
% 2.04/0.67    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0)) ) | ~spl7_3),
% 2.04/0.67    inference(resolution,[],[f96,f121])).
% 2.04/0.67  fof(f96,plain,(
% 2.04/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f53])).
% 2.04/0.67  fof(f436,plain,(
% 2.04/0.67    spl7_1 | spl7_4 | spl7_52 | ~spl7_3),
% 2.04/0.67    inference(avatar_split_clause,[],[f429,f119,f434,f124,f109])).
% 2.04/0.67  fof(f429,plain,(
% 2.04/0.67    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3))) ) | ~spl7_3),
% 2.04/0.67    inference(resolution,[],[f95,f121])).
% 2.04/0.67  fof(f95,plain,(
% 2.04/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 2.04/0.67    inference(cnf_transformation,[],[f53])).
% 2.04/0.67  fof(f428,plain,(
% 2.04/0.67    ~spl7_23 | spl7_51 | ~spl7_44),
% 2.04/0.67    inference(avatar_split_clause,[],[f408,f385,f426,f221])).
% 2.04/0.67  fof(f408,plain,(
% 2.04/0.67    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~v1_relat_1(sK4) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl7_44),
% 2.04/0.67    inference(superposition,[],[f76,f387])).
% 2.04/0.67  fof(f400,plain,(
% 2.04/0.67    spl7_46 | ~spl7_10 | ~spl7_8),
% 2.04/0.67    inference(avatar_split_clause,[],[f395,f144,f154,f398])).
% 2.04/0.67  fof(f395,plain,(
% 2.04/0.67    ( ! [X0] : (~v1_funct_1(sK4) | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl7_8),
% 2.04/0.67    inference(resolution,[],[f94,f146])).
% 2.04/0.67  fof(f388,plain,(
% 2.04/0.67    ~spl7_23 | spl7_44 | ~spl7_33 | ~spl7_42),
% 2.04/0.67    inference(avatar_split_clause,[],[f383,f374,f281,f385,f221])).
% 2.04/0.67  fof(f281,plain,(
% 2.04/0.67    spl7_33 <=> v4_relat_1(sK4,sK2)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 2.04/0.67  fof(f374,plain,(
% 2.04/0.67    spl7_42 <=> v1_partfun1(sK4,sK2)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 2.04/0.67  fof(f383,plain,(
% 2.04/0.67    ~v4_relat_1(sK4,sK2) | sK2 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl7_42),
% 2.04/0.67    inference(resolution,[],[f376,f87])).
% 2.04/0.67  fof(f376,plain,(
% 2.04/0.67    v1_partfun1(sK4,sK2) | ~spl7_42),
% 2.04/0.67    inference(avatar_component_clause,[],[f374])).
% 2.04/0.67  fof(f377,plain,(
% 2.04/0.67    spl7_42 | ~spl7_9 | ~spl7_10 | spl7_2 | ~spl7_8),
% 2.04/0.67    inference(avatar_split_clause,[],[f371,f144,f114,f154,f149,f374])).
% 2.04/0.67  fof(f371,plain,(
% 2.04/0.67    v1_xboole_0(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2) | ~spl7_8),
% 2.04/0.67    inference(resolution,[],[f80,f146])).
% 2.04/0.67  fof(f309,plain,(
% 2.04/0.67    spl7_36 | ~spl7_35),
% 2.04/0.67    inference(avatar_split_clause,[],[f304,f299,f306])).
% 2.04/0.67  fof(f304,plain,(
% 2.04/0.67    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl7_35),
% 2.04/0.67    inference(resolution,[],[f301,f100])).
% 2.04/0.67  fof(f100,plain,(
% 2.04/0.67    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.04/0.67    inference(definition_unfolding,[],[f89,f79])).
% 2.04/0.67  fof(f89,plain,(
% 2.04/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f1])).
% 2.04/0.67  fof(f1,axiom,(
% 2.04/0.67    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.04/0.67  fof(f302,plain,(
% 2.04/0.67    spl7_4 | spl7_35 | spl7_7 | ~spl7_5),
% 2.04/0.67    inference(avatar_split_clause,[],[f297,f129,f139,f299,f124])).
% 2.04/0.67  fof(f129,plain,(
% 2.04/0.67    spl7_5 <=> r1_subset_1(sK2,sK3)),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.04/0.67  fof(f297,plain,(
% 2.04/0.67    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | ~spl7_5),
% 2.04/0.67    inference(resolution,[],[f85,f131])).
% 2.04/0.67  fof(f131,plain,(
% 2.04/0.67    r1_subset_1(sK2,sK3) | ~spl7_5),
% 2.04/0.67    inference(avatar_component_clause,[],[f129])).
% 2.04/0.67  fof(f85,plain,(
% 2.04/0.67    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f42])).
% 2.04/0.67  fof(f42,plain,(
% 2.04/0.67    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.04/0.67    inference(flattening,[],[f41])).
% 2.04/0.67  fof(f41,plain,(
% 2.04/0.67    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.04/0.67    inference(ennf_transformation,[],[f13])).
% 2.04/0.67  fof(f13,axiom,(
% 2.04/0.67    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 2.04/0.67  fof(f284,plain,(
% 2.04/0.67    spl7_33 | ~spl7_8),
% 2.04/0.67    inference(avatar_split_clause,[],[f278,f144,f281])).
% 2.04/0.67  fof(f278,plain,(
% 2.04/0.67    v4_relat_1(sK4,sK2) | ~spl7_8),
% 2.04/0.67    inference(resolution,[],[f93,f146])).
% 2.04/0.67  fof(f247,plain,(
% 2.04/0.67    spl7_27 | ~spl7_23),
% 2.04/0.67    inference(avatar_split_clause,[],[f232,f221,f244])).
% 2.04/0.67  fof(f244,plain,(
% 2.04/0.67    spl7_27 <=> sK4 = k7_relat_1(sK4,k1_relat_1(sK4))),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 2.04/0.67  fof(f232,plain,(
% 2.04/0.67    sK4 = k7_relat_1(sK4,k1_relat_1(sK4)) | ~spl7_23),
% 2.04/0.67    inference(resolution,[],[f223,f73])).
% 2.04/0.67  fof(f242,plain,(
% 2.04/0.67    spl7_25 | ~spl7_26 | ~spl7_23),
% 2.04/0.67    inference(avatar_split_clause,[],[f230,f221,f239,f235])).
% 2.04/0.67  fof(f235,plain,(
% 2.04/0.67    spl7_25 <=> k1_xboole_0 = sK4),
% 2.04/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 2.04/0.67  fof(f230,plain,(
% 2.04/0.67    k1_xboole_0 != k1_relat_1(sK4) | k1_xboole_0 = sK4 | ~spl7_23),
% 2.04/0.67    inference(resolution,[],[f223,f74])).
% 2.04/0.67  fof(f74,plain,(
% 2.04/0.67    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 2.04/0.67    inference(cnf_transformation,[],[f32])).
% 2.04/0.67  fof(f32,plain,(
% 2.04/0.67    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.04/0.67    inference(flattening,[],[f31])).
% 2.04/0.67  fof(f31,plain,(
% 2.04/0.67    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.04/0.67    inference(ennf_transformation,[],[f9])).
% 2.04/0.67  fof(f9,axiom,(
% 2.04/0.67    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 2.04/0.67  fof(f229,plain,(
% 2.04/0.67    spl7_24 | ~spl7_11),
% 2.04/0.67    inference(avatar_split_clause,[],[f219,f159,f226])).
% 2.04/0.67  fof(f219,plain,(
% 2.04/0.67    v1_relat_1(sK5) | ~spl7_11),
% 2.04/0.67    inference(resolution,[],[f92,f161])).
% 2.04/0.67  fof(f92,plain,(
% 2.04/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.04/0.67    inference(cnf_transformation,[],[f48])).
% 2.04/0.67  fof(f48,plain,(
% 2.04/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/0.67    inference(ennf_transformation,[],[f14])).
% 2.04/0.67  fof(f14,axiom,(
% 2.04/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.04/0.67  fof(f224,plain,(
% 2.04/0.67    spl7_23 | ~spl7_8),
% 2.04/0.67    inference(avatar_split_clause,[],[f218,f144,f221])).
% 2.04/0.67  fof(f218,plain,(
% 2.04/0.67    v1_relat_1(sK4) | ~spl7_8),
% 2.04/0.67    inference(resolution,[],[f92,f146])).
% 2.04/0.67  fof(f195,plain,(
% 2.04/0.67    spl7_18),
% 2.04/0.67    inference(avatar_split_clause,[],[f68,f192])).
% 2.04/0.67  fof(f68,plain,(
% 2.04/0.67    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.04/0.67    inference(cnf_transformation,[],[f8])).
% 2.04/0.67  fof(f8,axiom,(
% 2.04/0.67    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 2.04/0.67  fof(f185,plain,(
% 2.04/0.67    ~spl7_14 | ~spl7_15 | ~spl7_16),
% 2.04/0.67    inference(avatar_split_clause,[],[f54,f182,f178,f174])).
% 2.04/0.67  fof(f54,plain,(
% 2.04/0.67    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 2.04/0.67    inference(cnf_transformation,[],[f27])).
% 2.04/0.67  fof(f27,plain,(
% 2.04/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.04/0.67    inference(flattening,[],[f26])).
% 2.04/0.67  fof(f26,plain,(
% 2.04/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.04/0.67    inference(ennf_transformation,[],[f23])).
% 2.04/0.67  fof(f23,negated_conjecture,(
% 2.04/0.67    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 2.04/0.67    inference(negated_conjecture,[],[f22])).
% 2.04/0.67  fof(f22,conjecture,(
% 2.04/0.67    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 2.04/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 2.04/0.67  fof(f172,plain,(
% 2.04/0.67    spl7_13),
% 2.04/0.67    inference(avatar_split_clause,[],[f55,f169])).
% 2.04/0.67  fof(f55,plain,(
% 2.04/0.67    v1_funct_1(sK5)),
% 2.04/0.67    inference(cnf_transformation,[],[f27])).
% 2.04/0.67  fof(f167,plain,(
% 2.04/0.67    spl7_12),
% 2.04/0.67    inference(avatar_split_clause,[],[f56,f164])).
% 2.04/0.67  fof(f56,plain,(
% 2.04/0.67    v1_funct_2(sK5,sK3,sK1)),
% 2.04/0.67    inference(cnf_transformation,[],[f27])).
% 2.04/0.67  fof(f162,plain,(
% 2.04/0.67    spl7_11),
% 2.04/0.67    inference(avatar_split_clause,[],[f57,f159])).
% 2.04/0.67  fof(f57,plain,(
% 2.04/0.67    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.04/0.67    inference(cnf_transformation,[],[f27])).
% 2.04/0.67  fof(f157,plain,(
% 2.04/0.67    spl7_10),
% 2.04/0.67    inference(avatar_split_clause,[],[f58,f154])).
% 2.04/0.67  fof(f58,plain,(
% 2.04/0.67    v1_funct_1(sK4)),
% 2.04/0.67    inference(cnf_transformation,[],[f27])).
% 2.04/0.67  fof(f152,plain,(
% 2.04/0.67    spl7_9),
% 2.04/0.67    inference(avatar_split_clause,[],[f59,f149])).
% 2.04/0.67  fof(f59,plain,(
% 2.04/0.67    v1_funct_2(sK4,sK2,sK1)),
% 2.04/0.67    inference(cnf_transformation,[],[f27])).
% 2.04/0.67  fof(f147,plain,(
% 2.04/0.67    spl7_8),
% 2.04/0.67    inference(avatar_split_clause,[],[f60,f144])).
% 2.04/0.67  fof(f60,plain,(
% 2.04/0.67    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.04/0.67    inference(cnf_transformation,[],[f27])).
% 2.04/0.67  fof(f142,plain,(
% 2.04/0.67    ~spl7_7),
% 2.04/0.67    inference(avatar_split_clause,[],[f61,f139])).
% 2.04/0.67  fof(f61,plain,(
% 2.04/0.67    ~v1_xboole_0(sK3)),
% 2.04/0.67    inference(cnf_transformation,[],[f27])).
% 2.04/0.67  fof(f137,plain,(
% 2.04/0.67    spl7_6),
% 2.04/0.67    inference(avatar_split_clause,[],[f62,f134])).
% 2.04/0.67  fof(f62,plain,(
% 2.04/0.67    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.04/0.67    inference(cnf_transformation,[],[f27])).
% 2.04/0.67  fof(f132,plain,(
% 2.04/0.67    spl7_5),
% 2.04/0.67    inference(avatar_split_clause,[],[f63,f129])).
% 2.04/0.67  fof(f63,plain,(
% 2.04/0.67    r1_subset_1(sK2,sK3)),
% 2.04/0.67    inference(cnf_transformation,[],[f27])).
% 2.04/0.67  fof(f127,plain,(
% 2.04/0.67    ~spl7_4),
% 2.04/0.67    inference(avatar_split_clause,[],[f64,f124])).
% 2.04/0.67  fof(f64,plain,(
% 2.04/0.67    ~v1_xboole_0(sK2)),
% 2.04/0.67    inference(cnf_transformation,[],[f27])).
% 2.04/0.67  fof(f122,plain,(
% 2.04/0.67    spl7_3),
% 2.04/0.67    inference(avatar_split_clause,[],[f65,f119])).
% 2.04/0.67  fof(f65,plain,(
% 2.04/0.67    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.04/0.67    inference(cnf_transformation,[],[f27])).
% 2.04/0.67  fof(f117,plain,(
% 2.04/0.67    ~spl7_2),
% 2.04/0.67    inference(avatar_split_clause,[],[f66,f114])).
% 2.04/0.67  fof(f66,plain,(
% 2.04/0.67    ~v1_xboole_0(sK1)),
% 2.04/0.67    inference(cnf_transformation,[],[f27])).
% 2.04/0.67  fof(f112,plain,(
% 2.04/0.67    ~spl7_1),
% 2.04/0.67    inference(avatar_split_clause,[],[f67,f109])).
% 2.04/0.67  fof(f67,plain,(
% 2.04/0.67    ~v1_xboole_0(sK0)),
% 2.04/0.67    inference(cnf_transformation,[],[f27])).
% 2.04/0.67  % SZS output end Proof for theBenchmark
% 2.04/0.67  % (4865)------------------------------
% 2.04/0.67  % (4865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.67  % (4865)Termination reason: Refutation
% 2.04/0.67  
% 2.04/0.67  % (4865)Memory used [KB]: 12281
% 2.04/0.67  % (4865)Time elapsed: 0.216 s
% 2.04/0.67  % (4865)------------------------------
% 2.04/0.67  % (4865)------------------------------
% 2.04/0.67  % (4848)Success in time 0.299 s
%------------------------------------------------------------------------------
