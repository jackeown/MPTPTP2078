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
% DateTime   : Thu Dec  3 13:17:27 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :  324 ( 722 expanded)
%              Number of leaves         :   78 ( 346 expanded)
%              Depth                    :   14
%              Number of atoms          : 1530 (3300 expanded)
%              Number of equality atoms :  206 ( 517 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1503,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f116,f121,f126,f131,f136,f141,f146,f151,f156,f161,f166,f171,f184,f189,f194,f199,f228,f233,f260,f298,f303,f315,f322,f369,f374,f380,f386,f390,f396,f410,f414,f422,f442,f458,f480,f486,f489,f510,f511,f525,f554,f575,f598,f635,f664,f710,f751,f791,f820,f880,f911,f963,f1416,f1424,f1502])).

fof(f1502,plain,
    ( ~ spl7_108
    | ~ spl7_6
    | spl7_16
    | ~ spl7_37
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_112 ),
    inference(avatar_split_clause,[],[f1501,f960,f388,f384,f319,f181,f133,f908])).

fof(f908,plain,
    ( spl7_108
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f133,plain,
    ( spl7_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f181,plain,
    ( spl7_16
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f319,plain,
    ( spl7_37
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f384,plain,
    ( spl7_44
  <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f388,plain,
    ( spl7_45
  <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f960,plain,
    ( spl7_112
  <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f1501,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_6
    | spl7_16
    | ~ spl7_37
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_112 ),
    inference(forward_demodulation,[],[f1500,f962])).

fof(f962,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl7_112 ),
    inference(avatar_component_clause,[],[f960])).

fof(f1500,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ spl7_6
    | spl7_16
    | ~ spl7_37
    | ~ spl7_44
    | ~ spl7_45 ),
    inference(forward_demodulation,[],[f1499,f385])).

fof(f385,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f384])).

fof(f1499,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl7_6
    | spl7_16
    | ~ spl7_37
    | ~ spl7_45 ),
    inference(forward_demodulation,[],[f1498,f321])).

fof(f321,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f319])).

fof(f1498,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl7_6
    | spl7_16
    | ~ spl7_45 ),
    inference(forward_demodulation,[],[f1497,f354])).

fof(f354,plain,
    ( ! [X1] : k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))
    | ~ spl7_6 ),
    inference(resolution,[],[f101,f135])).

fof(f135,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f92,f81])).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f92,plain,(
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

fof(f1497,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl7_16
    | ~ spl7_45 ),
    inference(forward_demodulation,[],[f183,f389])).

fof(f389,plain,
    ( ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f388])).

fof(f183,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f181])).

fof(f1424,plain,
    ( spl7_14
    | spl7_1
    | ~ spl7_99
    | ~ spl7_95
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
    | ~ spl7_37
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_104
    | ~ spl7_108
    | ~ spl7_112 ),
    inference(avatar_split_clause,[],[f1423,f960,f908,f877,f388,f384,f319,f133,f113,f123,f118,f138,f133,f153,f148,f143,f168,f163,f158,f788,f817,f108,f173])).

fof(f173,plain,
    ( spl7_14
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f108,plain,
    ( spl7_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f817,plain,
    ( spl7_99
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_99])])).

fof(f788,plain,
    ( spl7_95
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f158,plain,
    ( spl7_11
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f163,plain,
    ( spl7_12
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f168,plain,
    ( spl7_13
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f143,plain,
    ( spl7_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f148,plain,
    ( spl7_9
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f153,plain,
    ( spl7_10
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f138,plain,
    ( spl7_7
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f118,plain,
    ( spl7_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f123,plain,
    ( spl7_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f113,plain,
    ( spl7_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f877,plain,
    ( spl7_104
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f1423,plain,
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
    | ~ spl7_37
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_104
    | ~ spl7_108
    | ~ spl7_112 ),
    inference(trivial_inequality_removal,[],[f1422])).

fof(f1422,plain,
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
    | ~ spl7_37
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_104
    | ~ spl7_108
    | ~ spl7_112 ),
    inference(forward_demodulation,[],[f1421,f910])).

fof(f910,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_108 ),
    inference(avatar_component_clause,[],[f908])).

fof(f1421,plain,
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
    | ~ spl7_37
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_104
    | ~ spl7_112 ),
    inference(forward_demodulation,[],[f1420,f962])).

fof(f1420,plain,
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
    | ~ spl7_37
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_104 ),
    inference(forward_demodulation,[],[f1419,f385])).

fof(f1419,plain,
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
    | ~ spl7_37
    | ~ spl7_45
    | ~ spl7_104 ),
    inference(forward_demodulation,[],[f1418,f321])).

fof(f1418,plain,
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
    | ~ spl7_104 ),
    inference(forward_demodulation,[],[f1417,f354])).

fof(f1417,plain,
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
    | ~ spl7_104 ),
    inference(forward_demodulation,[],[f1393,f389])).

fof(f1393,plain,
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
    | ~ spl7_104 ),
    inference(resolution,[],[f879,f104])).

fof(f104,plain,(
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

fof(f879,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl7_104 ),
    inference(avatar_component_clause,[],[f877])).

fof(f1416,plain,
    ( spl7_15
    | spl7_1
    | ~ spl7_99
    | ~ spl7_95
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
    | ~ spl7_37
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_104
    | ~ spl7_108
    | ~ spl7_112 ),
    inference(avatar_split_clause,[],[f1415,f960,f908,f877,f388,f384,f319,f133,f113,f123,f118,f138,f133,f153,f148,f143,f168,f163,f158,f788,f817,f108,f177])).

fof(f177,plain,
    ( spl7_15
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f1415,plain,
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
    | ~ spl7_37
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_104
    | ~ spl7_108
    | ~ spl7_112 ),
    inference(trivial_inequality_removal,[],[f1414])).

fof(f1414,plain,
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
    | ~ spl7_37
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_104
    | ~ spl7_108
    | ~ spl7_112 ),
    inference(forward_demodulation,[],[f1413,f910])).

fof(f1413,plain,
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
    | ~ spl7_37
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_104
    | ~ spl7_112 ),
    inference(forward_demodulation,[],[f1412,f962])).

fof(f1412,plain,
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
    | ~ spl7_37
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_104 ),
    inference(forward_demodulation,[],[f1411,f385])).

fof(f1411,plain,
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
    | ~ spl7_37
    | ~ spl7_45
    | ~ spl7_104 ),
    inference(forward_demodulation,[],[f1410,f321])).

fof(f1410,plain,
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
    | ~ spl7_104 ),
    inference(forward_demodulation,[],[f1409,f354])).

fof(f1409,plain,
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
    | ~ spl7_104 ),
    inference(forward_demodulation,[],[f1392,f389])).

fof(f1392,plain,
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
    | ~ spl7_104 ),
    inference(resolution,[],[f879,f105])).

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

fof(f963,plain,
    ( spl7_112
    | ~ spl7_25
    | ~ spl7_90 ),
    inference(avatar_split_clause,[],[f958,f745,f230,f960])).

fof(f230,plain,
    ( spl7_25
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f745,plain,
    ( spl7_90
  <=> k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f958,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl7_25
    | ~ spl7_90 ),
    inference(trivial_inequality_removal,[],[f952])).

fof(f952,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl7_25
    | ~ spl7_90 ),
    inference(superposition,[],[f914,f747])).

fof(f747,plain,
    ( k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0)
    | ~ spl7_90 ),
    inference(avatar_component_clause,[],[f745])).

fof(f914,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK5,X0)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl7_25 ),
    inference(superposition,[],[f287,f306])).

fof(f306,plain,
    ( ! [X1] : k2_relat_1(k7_relat_1(sK5,X1)) = k9_relat_1(sK5,X1)
    | ~ spl7_25 ),
    inference(resolution,[],[f85,f232])).

fof(f232,plain,
    ( v1_relat_1(sK5)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f230])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f287,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_relat_1(k7_relat_1(sK5,X0))
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl7_25 ),
    inference(resolution,[],[f244,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f244,plain,
    ( ! [X1] : v1_relat_1(k7_relat_1(sK5,X1))
    | ~ spl7_25 ),
    inference(resolution,[],[f232,f83])).

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

fof(f911,plain,
    ( spl7_108
    | ~ spl7_24
    | ~ spl7_85 ),
    inference(avatar_split_clause,[],[f905,f707,f225,f908])).

fof(f225,plain,
    ( spl7_24
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f707,plain,
    ( spl7_85
  <=> k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f905,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_85 ),
    inference(trivial_inequality_removal,[],[f904])).

fof(f904,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_85 ),
    inference(superposition,[],[f901,f709])).

fof(f709,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0)
    | ~ spl7_85 ),
    inference(avatar_component_clause,[],[f707])).

fof(f901,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK4,X0)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl7_24 ),
    inference(superposition,[],[f276,f305])).

fof(f305,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0)
    | ~ spl7_24 ),
    inference(resolution,[],[f85,f227])).

fof(f227,plain,
    ( v1_relat_1(sK4)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f225])).

fof(f276,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_relat_1(k7_relat_1(sK4,X0))
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl7_24 ),
    inference(resolution,[],[f76,f236])).

fof(f236,plain,
    ( ! [X1] : v1_relat_1(k7_relat_1(sK4,X1))
    | ~ spl7_24 ),
    inference(resolution,[],[f227,f83])).

fof(f880,plain,
    ( spl7_104
    | ~ spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f875,f662,f143,f148,f153,f877])).

fof(f662,plain,
    ( spl7_82
  <=> ! [X1] :
        ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f875,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl7_8
    | ~ spl7_82 ),
    inference(resolution,[],[f663,f145])).

fof(f145,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f663,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) )
    | ~ spl7_82 ),
    inference(avatar_component_clause,[],[f662])).

fof(f820,plain,
    ( spl7_99
    | ~ spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_78 ),
    inference(avatar_split_clause,[],[f815,f633,f143,f148,f153,f817])).

fof(f633,plain,
    ( spl7_78
  <=> ! [X1] :
        ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f815,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl7_8
    | ~ spl7_78 ),
    inference(resolution,[],[f634,f145])).

fof(f634,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) )
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f633])).

fof(f791,plain,
    ( spl7_95
    | ~ spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f786,f596,f143,f148,f153,f788])).

fof(f596,plain,
    ( spl7_72
  <=> ! [X1] :
        ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f786,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl7_8
    | ~ spl7_72 ),
    inference(resolution,[],[f597,f145])).

fof(f597,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) )
    | ~ spl7_72 ),
    inference(avatar_component_clause,[],[f596])).

fof(f751,plain,
    ( spl7_90
    | ~ spl7_25
    | ~ spl7_66
    | ~ spl7_68
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f750,f572,f551,f522,f230,f745])).

fof(f522,plain,
    ( spl7_66
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f551,plain,
    ( spl7_68
  <=> k1_xboole_0 = k7_relat_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f572,plain,
    ( spl7_70
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f750,plain,
    ( k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0)
    | ~ spl7_25
    | ~ spl7_66
    | ~ spl7_68
    | ~ spl7_70 ),
    inference(forward_demodulation,[],[f749,f524])).

fof(f524,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f522])).

fof(f749,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0)
    | ~ spl7_25
    | ~ spl7_68
    | ~ spl7_70 ),
    inference(forward_demodulation,[],[f736,f553])).

fof(f553,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl7_68 ),
    inference(avatar_component_clause,[],[f551])).

fof(f736,plain,
    ( k9_relat_1(sK5,k1_xboole_0) = k9_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0)
    | ~ spl7_25
    | ~ spl7_70 ),
    inference(resolution,[],[f358,f574])).

fof(f574,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f572])).

fof(f358,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k9_relat_1(k7_relat_1(sK5,X3),X2) = k9_relat_1(sK5,X2) )
    | ~ spl7_25 ),
    inference(resolution,[],[f78,f232])).

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

fof(f710,plain,
    ( spl7_85
    | ~ spl7_24
    | ~ spl7_62
    | ~ spl7_65
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f705,f522,f507,f483,f225,f707])).

fof(f483,plain,
    ( spl7_62
  <=> k1_xboole_0 = k7_relat_1(sK4,sK6(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f507,plain,
    ( spl7_65
  <=> r1_tarski(k1_xboole_0,sK6(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f705,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_62
    | ~ spl7_65
    | ~ spl7_66 ),
    inference(forward_demodulation,[],[f704,f524])).

fof(f704,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_62
    | ~ spl7_65 ),
    inference(forward_demodulation,[],[f701,f485])).

fof(f485,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK6(sK2))
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f483])).

fof(f701,plain,
    ( k9_relat_1(sK4,k1_xboole_0) = k9_relat_1(k7_relat_1(sK4,sK6(sK2)),k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_65 ),
    inference(resolution,[],[f357,f509])).

fof(f509,plain,
    ( r1_tarski(k1_xboole_0,sK6(sK2))
    | ~ spl7_65 ),
    inference(avatar_component_clause,[],[f507])).

fof(f357,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k9_relat_1(sK4,X0) = k9_relat_1(k7_relat_1(sK4,X1),X0) )
    | ~ spl7_24 ),
    inference(resolution,[],[f78,f227])).

fof(f664,plain,
    ( ~ spl7_6
    | ~ spl7_12
    | spl7_7
    | ~ spl7_13
    | spl7_2
    | spl7_82
    | ~ spl7_11
    | ~ spl7_57 ),
    inference(avatar_split_clause,[],[f656,f456,f158,f662,f113,f168,f138,f163,f133])).

fof(f456,plain,
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

fof(f656,plain,
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
    inference(resolution,[],[f457,f160])).

fof(f160,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f158])).

fof(f457,plain,
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
    inference(avatar_component_clause,[],[f456])).

fof(f635,plain,
    ( ~ spl7_6
    | ~ spl7_12
    | spl7_7
    | ~ spl7_13
    | spl7_2
    | spl7_78
    | ~ spl7_11
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f627,f440,f158,f633,f113,f168,f138,f163,f133])).

fof(f440,plain,
    ( spl7_54
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
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f627,plain,
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
    | ~ spl7_54 ),
    inference(resolution,[],[f441,f160])).

fof(f441,plain,
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
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f440])).

fof(f598,plain,
    ( ~ spl7_6
    | ~ spl7_12
    | spl7_7
    | ~ spl7_13
    | spl7_2
    | spl7_72
    | ~ spl7_11
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f590,f420,f158,f596,f113,f168,f138,f163,f133])).

fof(f420,plain,
    ( spl7_50
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
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f590,plain,
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
    | ~ spl7_50 ),
    inference(resolution,[],[f421,f160])).

fof(f421,plain,
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
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f420])).

fof(f575,plain,
    ( spl7_70
    | ~ spl7_19
    | ~ spl7_25
    | ~ spl7_68 ),
    inference(avatar_split_clause,[],[f570,f551,f230,f196,f572])).

fof(f196,plain,
    ( spl7_19
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f570,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl7_19
    | ~ spl7_25
    | ~ spl7_68 ),
    inference(forward_demodulation,[],[f562,f198])).

fof(f198,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f196])).

fof(f562,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK2)
    | ~ spl7_25
    | ~ spl7_68 ),
    inference(superposition,[],[f243,f553])).

fof(f243,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),X0)
    | ~ spl7_25 ),
    inference(resolution,[],[f232,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f554,plain,
    ( spl7_68
    | ~ spl7_36
    | ~ spl7_61 ),
    inference(avatar_split_clause,[],[f544,f478,f312,f551])).

fof(f312,plain,
    ( spl7_36
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f478,plain,
    ( spl7_61
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f544,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl7_36
    | ~ spl7_61 ),
    inference(resolution,[],[f479,f314])).

fof(f314,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f312])).

fof(f479,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl7_61 ),
    inference(avatar_component_clause,[],[f478])).

fof(f525,plain,
    ( spl7_66
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f520,f331,f196,f191,f522])).

fof(f191,plain,
    ( spl7_18
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f331,plain,
    ( spl7_39
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f520,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_39 ),
    inference(forward_demodulation,[],[f519,f193])).

fof(f193,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f191])).

fof(f519,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_19
    | ~ spl7_39 ),
    inference(forward_demodulation,[],[f512,f198])).

fof(f512,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl7_39 ),
    inference(resolution,[],[f332,f74])).

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

fof(f332,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f331])).

fof(f511,plain,
    ( spl7_39
    | ~ spl7_24
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f498,f483,f225,f331])).

fof(f498,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_62 ),
    inference(superposition,[],[f236,f485])).

fof(f510,plain,
    ( spl7_65
    | ~ spl7_19
    | ~ spl7_24
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f505,f483,f225,f196,f507])).

fof(f505,plain,
    ( r1_tarski(k1_xboole_0,sK6(sK2))
    | ~ spl7_19
    | ~ spl7_24
    | ~ spl7_62 ),
    inference(forward_demodulation,[],[f497,f198])).

fof(f497,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK6(sK2))
    | ~ spl7_24
    | ~ spl7_62 ),
    inference(superposition,[],[f235,f485])).

fof(f235,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0)
    | ~ spl7_24 ),
    inference(resolution,[],[f227,f84])).

fof(f489,plain,
    ( k1_xboole_0 != sK4
    | sK2 != k1_relat_1(sK4)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f486,plain,
    ( spl7_48
    | spl7_62
    | ~ spl7_49 ),
    inference(avatar_split_clause,[],[f481,f412,f483,f407])).

fof(f407,plain,
    ( spl7_48
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f412,plain,
    ( spl7_49
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | k1_xboole_0 = k7_relat_1(sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f481,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK6(sK2))
    | k1_xboole_0 = sK2
    | ~ spl7_49 ),
    inference(resolution,[],[f413,f80])).

fof(f80,plain,(
    ! [X0] :
      ( r1_xboole_0(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r1_xboole_0(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r1_xboole_0(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f413,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f412])).

fof(f480,plain,
    ( ~ spl7_25
    | spl7_61
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f465,f393,f478,f230])).

fof(f393,plain,
    ( spl7_46
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f465,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK3)
        | ~ v1_relat_1(sK5)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl7_46 ),
    inference(superposition,[],[f77,f395])).

fof(f395,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f393])).

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

fof(f458,plain,
    ( spl7_1
    | spl7_4
    | spl7_57
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f451,f118,f456,f123,f108])).

fof(f451,plain,
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
    inference(resolution,[],[f98,f120])).

fof(f120,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f118])).

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

fof(f442,plain,
    ( spl7_1
    | spl7_4
    | spl7_54
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f435,f118,f440,f123,f108])).

fof(f435,plain,
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
    inference(resolution,[],[f97,f120])).

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
      | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f422,plain,
    ( spl7_1
    | spl7_4
    | spl7_50
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f415,f118,f420,f123,f108])).

fof(f415,plain,
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
    inference(resolution,[],[f96,f120])).

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
      | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f414,plain,
    ( ~ spl7_24
    | spl7_49
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f399,f377,f412,f225])).

fof(f377,plain,
    ( spl7_43
  <=> sK2 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f399,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | ~ v1_relat_1(sK4)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl7_43 ),
    inference(superposition,[],[f77,f379])).

fof(f379,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f377])).

fof(f410,plain,
    ( ~ spl7_48
    | spl7_29
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f398,f377,f257,f407])).

fof(f257,plain,
    ( spl7_29
  <=> k1_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f398,plain,
    ( k1_xboole_0 != sK2
    | spl7_29
    | ~ spl7_43 ),
    inference(superposition,[],[f259,f379])).

fof(f259,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | spl7_29 ),
    inference(avatar_component_clause,[],[f257])).

fof(f396,plain,
    ( ~ spl7_25
    | spl7_46
    | ~ spl7_35
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f391,f371,f300,f393,f230])).

fof(f300,plain,
    ( spl7_35
  <=> v4_relat_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f371,plain,
    ( spl7_42
  <=> v1_partfun1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f391,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl7_42 ),
    inference(resolution,[],[f373,f89])).

fof(f89,plain,(
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

fof(f373,plain,
    ( v1_partfun1(sK5,sK3)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f371])).

fof(f390,plain,
    ( spl7_45
    | ~ spl7_13
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f382,f158,f168,f388])).

fof(f382,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK5)
        | k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) )
    | ~ spl7_11 ),
    inference(resolution,[],[f95,f160])).

fof(f95,plain,(
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

fof(f386,plain,
    ( spl7_44
    | ~ spl7_10
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f381,f143,f153,f384])).

fof(f381,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) )
    | ~ spl7_8 ),
    inference(resolution,[],[f95,f145])).

fof(f380,plain,
    ( ~ spl7_24
    | spl7_43
    | ~ spl7_34
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f375,f366,f295,f377,f225])).

fof(f295,plain,
    ( spl7_34
  <=> v4_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f366,plain,
    ( spl7_41
  <=> v1_partfun1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f375,plain,
    ( ~ v4_relat_1(sK4,sK2)
    | sK2 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl7_41 ),
    inference(resolution,[],[f368,f89])).

fof(f368,plain,
    ( v1_partfun1(sK4,sK2)
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f366])).

fof(f374,plain,
    ( spl7_42
    | ~ spl7_12
    | ~ spl7_13
    | spl7_2
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f364,f158,f113,f168,f163,f371])).

fof(f364,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | ~ spl7_11 ),
    inference(resolution,[],[f82,f160])).

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

fof(f369,plain,
    ( spl7_41
    | ~ spl7_9
    | ~ spl7_10
    | spl7_2
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f363,f143,f113,f153,f148,f366])).

fof(f363,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f82,f145])).

fof(f322,plain,
    ( spl7_37
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f317,f312,f319])).

fof(f317,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl7_36 ),
    inference(resolution,[],[f314,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f91,f81])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f315,plain,
    ( spl7_4
    | spl7_36
    | spl7_7
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f310,f128,f138,f312,f123])).

fof(f128,plain,
    ( spl7_5
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f310,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2)
    | ~ spl7_5 ),
    inference(resolution,[],[f87,f130])).

fof(f130,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f87,plain,(
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

fof(f303,plain,
    ( spl7_35
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f293,f158,f300])).

fof(f293,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl7_11 ),
    inference(resolution,[],[f94,f160])).

fof(f94,plain,(
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

fof(f298,plain,
    ( spl7_34
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f292,f143,f295])).

fof(f292,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f94,f145])).

fof(f260,plain,
    ( spl7_28
    | ~ spl7_29
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f250,f225,f257,f253])).

fof(f253,plain,
    ( spl7_28
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f250,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | k1_xboole_0 = sK4
    | ~ spl7_24 ),
    inference(resolution,[],[f75,f227])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f233,plain,
    ( spl7_25
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f223,f158,f230])).

fof(f223,plain,
    ( v1_relat_1(sK5)
    | ~ spl7_11 ),
    inference(resolution,[],[f93,f160])).

fof(f93,plain,(
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

fof(f228,plain,
    ( spl7_24
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f222,f143,f225])).

fof(f222,plain,
    ( v1_relat_1(sK4)
    | ~ spl7_8 ),
    inference(resolution,[],[f93,f145])).

fof(f199,plain,(
    spl7_19 ),
    inference(avatar_split_clause,[],[f69,f196])).

fof(f69,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f194,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f70,f191])).

fof(f70,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f189,plain,(
    spl7_17 ),
    inference(avatar_split_clause,[],[f68,f186])).

fof(f186,plain,
    ( spl7_17
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f184,plain,
    ( ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f54,f181,f177,f173])).

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

fof(f171,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f55,f168])).

fof(f55,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f166,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f56,f163])).

fof(f56,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f161,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f57,f158])).

fof(f57,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f156,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f58,f153])).

fof(f58,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f151,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f59,f148])).

fof(f59,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f146,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f60,f143])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f141,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f61,f138])).

fof(f61,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f136,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f62,f133])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f131,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f63,f128])).

fof(f63,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f126,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f64,f123])).

fof(f64,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f121,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f65,f118])).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f116,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f66,f113])).

fof(f66,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f111,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f67,f108])).

fof(f67,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:33:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (25161)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (25165)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (25166)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (25164)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (25163)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (25162)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (25177)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.52  % (25169)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (25174)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (25160)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (25183)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (25175)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (25167)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (25168)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (25177)Refutation not found, incomplete strategy% (25177)------------------------------
% 0.22/0.54  % (25177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (25177)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (25177)Memory used [KB]: 10746
% 0.22/0.54  % (25177)Time elapsed: 0.118 s
% 0.22/0.54  % (25177)------------------------------
% 0.22/0.54  % (25177)------------------------------
% 0.22/0.54  % (25186)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (25178)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (25182)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (25184)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (25170)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (25185)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (25179)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (25176)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (25181)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (25189)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (25180)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (25173)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (25172)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (25171)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.49/0.56  % (25188)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.49/0.56  % (25187)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.62/0.59  % (25182)Refutation not found, incomplete strategy% (25182)------------------------------
% 1.62/0.59  % (25182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  % (25170)Refutation not found, incomplete strategy% (25170)------------------------------
% 1.62/0.60  % (25170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  % (25182)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.60  
% 1.62/0.60  % (25182)Memory used [KB]: 11513
% 1.62/0.60  % (25182)Time elapsed: 0.180 s
% 1.62/0.60  % (25182)------------------------------
% 1.62/0.60  % (25182)------------------------------
% 1.62/0.62  % (25170)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.62  
% 1.62/0.62  % (25170)Memory used [KB]: 11513
% 1.62/0.62  % (25170)Time elapsed: 0.186 s
% 1.62/0.62  % (25170)------------------------------
% 1.62/0.62  % (25170)------------------------------
% 2.00/0.63  % (25176)Refutation found. Thanks to Tanya!
% 2.00/0.63  % SZS status Theorem for theBenchmark
% 2.00/0.63  % SZS output start Proof for theBenchmark
% 2.00/0.63  fof(f1503,plain,(
% 2.00/0.63    $false),
% 2.00/0.63    inference(avatar_sat_refutation,[],[f111,f116,f121,f126,f131,f136,f141,f146,f151,f156,f161,f166,f171,f184,f189,f194,f199,f228,f233,f260,f298,f303,f315,f322,f369,f374,f380,f386,f390,f396,f410,f414,f422,f442,f458,f480,f486,f489,f510,f511,f525,f554,f575,f598,f635,f664,f710,f751,f791,f820,f880,f911,f963,f1416,f1424,f1502])).
% 2.00/0.63  fof(f1502,plain,(
% 2.00/0.63    ~spl7_108 | ~spl7_6 | spl7_16 | ~spl7_37 | ~spl7_44 | ~spl7_45 | ~spl7_112),
% 2.00/0.63    inference(avatar_split_clause,[],[f1501,f960,f388,f384,f319,f181,f133,f908])).
% 2.00/0.63  fof(f908,plain,(
% 2.00/0.63    spl7_108 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).
% 2.00/0.63  fof(f133,plain,(
% 2.00/0.63    spl7_6 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 2.00/0.63  fof(f181,plain,(
% 2.00/0.63    spl7_16 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 2.00/0.63  fof(f319,plain,(
% 2.00/0.63    spl7_37 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 2.00/0.63  fof(f384,plain,(
% 2.00/0.63    spl7_44 <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 2.00/0.63  fof(f388,plain,(
% 2.00/0.63    spl7_45 <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 2.00/0.63  fof(f960,plain,(
% 2.00/0.63    spl7_112 <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).
% 2.00/0.63  fof(f1501,plain,(
% 2.00/0.63    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | (~spl7_6 | spl7_16 | ~spl7_37 | ~spl7_44 | ~spl7_45 | ~spl7_112)),
% 2.00/0.63    inference(forward_demodulation,[],[f1500,f962])).
% 2.00/0.63  fof(f962,plain,(
% 2.00/0.63    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | ~spl7_112),
% 2.00/0.63    inference(avatar_component_clause,[],[f960])).
% 2.00/0.63  fof(f1500,plain,(
% 2.00/0.63    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | (~spl7_6 | spl7_16 | ~spl7_37 | ~spl7_44 | ~spl7_45)),
% 2.00/0.63    inference(forward_demodulation,[],[f1499,f385])).
% 2.00/0.63  fof(f385,plain,(
% 2.00/0.63    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl7_44),
% 2.00/0.63    inference(avatar_component_clause,[],[f384])).
% 2.00/0.63  fof(f1499,plain,(
% 2.00/0.63    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (~spl7_6 | spl7_16 | ~spl7_37 | ~spl7_45)),
% 2.00/0.63    inference(forward_demodulation,[],[f1498,f321])).
% 2.00/0.63  fof(f321,plain,(
% 2.00/0.63    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl7_37),
% 2.00/0.63    inference(avatar_component_clause,[],[f319])).
% 2.00/0.63  fof(f1498,plain,(
% 2.00/0.63    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | (~spl7_6 | spl7_16 | ~spl7_45)),
% 2.00/0.63    inference(forward_demodulation,[],[f1497,f354])).
% 2.00/0.63  fof(f354,plain,(
% 2.00/0.63    ( ! [X1] : (k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))) ) | ~spl7_6),
% 2.00/0.63    inference(resolution,[],[f101,f135])).
% 2.00/0.63  fof(f135,plain,(
% 2.00/0.63    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl7_6),
% 2.00/0.63    inference(avatar_component_clause,[],[f133])).
% 2.00/0.63  fof(f101,plain,(
% 2.00/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 2.00/0.63    inference(definition_unfolding,[],[f92,f81])).
% 2.00/0.63  fof(f81,plain,(
% 2.00/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.00/0.63    inference(cnf_transformation,[],[f5])).
% 2.00/0.63  fof(f5,axiom,(
% 2.00/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.00/0.63  fof(f92,plain,(
% 2.00/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 2.00/0.63    inference(cnf_transformation,[],[f47])).
% 2.00/0.63  fof(f47,plain,(
% 2.00/0.63    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.00/0.63    inference(ennf_transformation,[],[f3])).
% 2.00/0.63  fof(f3,axiom,(
% 2.00/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.00/0.63  fof(f1497,plain,(
% 2.00/0.63    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (spl7_16 | ~spl7_45)),
% 2.00/0.63    inference(forward_demodulation,[],[f183,f389])).
% 2.00/0.63  fof(f389,plain,(
% 2.00/0.63    ( ! [X1] : (k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl7_45),
% 2.00/0.63    inference(avatar_component_clause,[],[f388])).
% 2.00/0.63  fof(f183,plain,(
% 2.00/0.63    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl7_16),
% 2.00/0.63    inference(avatar_component_clause,[],[f181])).
% 2.00/0.63  fof(f1424,plain,(
% 2.00/0.63    spl7_14 | spl7_1 | ~spl7_99 | ~spl7_95 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_6 | spl7_7 | ~spl7_3 | spl7_4 | spl7_2 | ~spl7_6 | ~spl7_37 | ~spl7_44 | ~spl7_45 | ~spl7_104 | ~spl7_108 | ~spl7_112),
% 2.00/0.63    inference(avatar_split_clause,[],[f1423,f960,f908,f877,f388,f384,f319,f133,f113,f123,f118,f138,f133,f153,f148,f143,f168,f163,f158,f788,f817,f108,f173])).
% 2.00/0.63  fof(f173,plain,(
% 2.00/0.63    spl7_14 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 2.00/0.63  fof(f108,plain,(
% 2.00/0.63    spl7_1 <=> v1_xboole_0(sK0)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.00/0.63  fof(f817,plain,(
% 2.00/0.63    spl7_99 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_99])])).
% 2.00/0.63  fof(f788,plain,(
% 2.00/0.63    spl7_95 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).
% 2.00/0.63  fof(f158,plain,(
% 2.00/0.63    spl7_11 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 2.00/0.63  fof(f163,plain,(
% 2.00/0.63    spl7_12 <=> v1_funct_2(sK5,sK3,sK1)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 2.00/0.63  fof(f168,plain,(
% 2.00/0.63    spl7_13 <=> v1_funct_1(sK5)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 2.00/0.63  fof(f143,plain,(
% 2.00/0.63    spl7_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 2.00/0.63  fof(f148,plain,(
% 2.00/0.63    spl7_9 <=> v1_funct_2(sK4,sK2,sK1)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 2.00/0.63  fof(f153,plain,(
% 2.00/0.63    spl7_10 <=> v1_funct_1(sK4)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 2.00/0.63  fof(f138,plain,(
% 2.00/0.63    spl7_7 <=> v1_xboole_0(sK3)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 2.00/0.63  fof(f118,plain,(
% 2.00/0.63    spl7_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.00/0.63  fof(f123,plain,(
% 2.00/0.63    spl7_4 <=> v1_xboole_0(sK2)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.00/0.63  fof(f113,plain,(
% 2.00/0.63    spl7_2 <=> v1_xboole_0(sK1)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.00/0.63  fof(f877,plain,(
% 2.00/0.63    spl7_104 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).
% 2.00/0.63  fof(f1423,plain,(
% 2.00/0.63    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_37 | ~spl7_44 | ~spl7_45 | ~spl7_104 | ~spl7_108 | ~spl7_112)),
% 2.00/0.63    inference(trivial_inequality_removal,[],[f1422])).
% 2.00/0.63  fof(f1422,plain,(
% 2.00/0.63    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_37 | ~spl7_44 | ~spl7_45 | ~spl7_104 | ~spl7_108 | ~spl7_112)),
% 2.00/0.63    inference(forward_demodulation,[],[f1421,f910])).
% 2.00/0.63  fof(f910,plain,(
% 2.00/0.63    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl7_108),
% 2.00/0.63    inference(avatar_component_clause,[],[f908])).
% 2.00/0.63  fof(f1421,plain,(
% 2.00/0.63    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_37 | ~spl7_44 | ~spl7_45 | ~spl7_104 | ~spl7_112)),
% 2.00/0.63    inference(forward_demodulation,[],[f1420,f962])).
% 2.00/0.63  fof(f1420,plain,(
% 2.00/0.63    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_37 | ~spl7_44 | ~spl7_45 | ~spl7_104)),
% 2.00/0.63    inference(forward_demodulation,[],[f1419,f385])).
% 2.00/0.63  fof(f1419,plain,(
% 2.00/0.63    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_37 | ~spl7_45 | ~spl7_104)),
% 2.00/0.63    inference(forward_demodulation,[],[f1418,f321])).
% 2.00/0.63  fof(f1418,plain,(
% 2.00/0.63    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_45 | ~spl7_104)),
% 2.00/0.63    inference(forward_demodulation,[],[f1417,f354])).
% 2.00/0.63  fof(f1417,plain,(
% 2.00/0.63    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_45 | ~spl7_104)),
% 2.00/0.63    inference(forward_demodulation,[],[f1393,f389])).
% 2.00/0.63  fof(f1393,plain,(
% 2.00/0.63    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~spl7_104),
% 2.00/0.63    inference(resolution,[],[f879,f104])).
% 2.00/0.63  fof(f104,plain,(
% 2.00/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 2.00/0.63    inference(equality_resolution,[],[f72])).
% 2.00/0.63  fof(f72,plain,(
% 2.00/0.63    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 2.00/0.63    inference(cnf_transformation,[],[f30])).
% 2.00/0.63  fof(f30,plain,(
% 2.00/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.00/0.63    inference(flattening,[],[f29])).
% 2.00/0.63  fof(f29,plain,(
% 2.00/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.00/0.63    inference(ennf_transformation,[],[f21])).
% 2.00/0.63  fof(f21,axiom,(
% 2.00/0.63    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).
% 2.00/0.63  fof(f879,plain,(
% 2.00/0.63    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl7_104),
% 2.00/0.63    inference(avatar_component_clause,[],[f877])).
% 2.00/0.63  fof(f1416,plain,(
% 2.00/0.63    spl7_15 | spl7_1 | ~spl7_99 | ~spl7_95 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_6 | spl7_7 | ~spl7_3 | spl7_4 | spl7_2 | ~spl7_6 | ~spl7_37 | ~spl7_44 | ~spl7_45 | ~spl7_104 | ~spl7_108 | ~spl7_112),
% 2.00/0.63    inference(avatar_split_clause,[],[f1415,f960,f908,f877,f388,f384,f319,f133,f113,f123,f118,f138,f133,f153,f148,f143,f168,f163,f158,f788,f817,f108,f177])).
% 2.00/0.63  fof(f177,plain,(
% 2.00/0.63    spl7_15 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 2.00/0.63  fof(f1415,plain,(
% 2.00/0.63    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_37 | ~spl7_44 | ~spl7_45 | ~spl7_104 | ~spl7_108 | ~spl7_112)),
% 2.00/0.63    inference(trivial_inequality_removal,[],[f1414])).
% 2.00/0.63  fof(f1414,plain,(
% 2.00/0.63    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_37 | ~spl7_44 | ~spl7_45 | ~spl7_104 | ~spl7_108 | ~spl7_112)),
% 2.00/0.63    inference(forward_demodulation,[],[f1413,f910])).
% 2.00/0.63  fof(f1413,plain,(
% 2.00/0.63    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_37 | ~spl7_44 | ~spl7_45 | ~spl7_104 | ~spl7_112)),
% 2.00/0.63    inference(forward_demodulation,[],[f1412,f962])).
% 2.00/0.63  fof(f1412,plain,(
% 2.00/0.63    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_37 | ~spl7_44 | ~spl7_45 | ~spl7_104)),
% 2.00/0.63    inference(forward_demodulation,[],[f1411,f385])).
% 2.00/0.63  fof(f1411,plain,(
% 2.00/0.63    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_37 | ~spl7_45 | ~spl7_104)),
% 2.00/0.63    inference(forward_demodulation,[],[f1410,f321])).
% 2.00/0.63  fof(f1410,plain,(
% 2.00/0.63    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_45 | ~spl7_104)),
% 2.00/0.63    inference(forward_demodulation,[],[f1409,f354])).
% 2.00/0.63  fof(f1409,plain,(
% 2.00/0.63    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_45 | ~spl7_104)),
% 2.00/0.63    inference(forward_demodulation,[],[f1392,f389])).
% 2.00/0.63  fof(f1392,plain,(
% 2.00/0.63    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~spl7_104),
% 2.00/0.63    inference(resolution,[],[f879,f105])).
% 2.00/0.63  fof(f105,plain,(
% 2.00/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 2.00/0.63    inference(equality_resolution,[],[f71])).
% 2.00/0.63  fof(f71,plain,(
% 2.00/0.63    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 2.00/0.63    inference(cnf_transformation,[],[f30])).
% 2.00/0.63  fof(f963,plain,(
% 2.00/0.63    spl7_112 | ~spl7_25 | ~spl7_90),
% 2.00/0.63    inference(avatar_split_clause,[],[f958,f745,f230,f960])).
% 2.00/0.63  fof(f230,plain,(
% 2.00/0.63    spl7_25 <=> v1_relat_1(sK5)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 2.00/0.63  fof(f745,plain,(
% 2.00/0.63    spl7_90 <=> k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).
% 2.00/0.63  fof(f958,plain,(
% 2.00/0.63    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | (~spl7_25 | ~spl7_90)),
% 2.00/0.63    inference(trivial_inequality_removal,[],[f952])).
% 2.00/0.63  fof(f952,plain,(
% 2.00/0.63    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | (~spl7_25 | ~spl7_90)),
% 2.00/0.63    inference(superposition,[],[f914,f747])).
% 2.00/0.63  fof(f747,plain,(
% 2.00/0.63    k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0) | ~spl7_90),
% 2.00/0.63    inference(avatar_component_clause,[],[f745])).
% 2.00/0.63  fof(f914,plain,(
% 2.00/0.63    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK5,X0) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl7_25),
% 2.00/0.63    inference(superposition,[],[f287,f306])).
% 2.00/0.63  fof(f306,plain,(
% 2.00/0.63    ( ! [X1] : (k2_relat_1(k7_relat_1(sK5,X1)) = k9_relat_1(sK5,X1)) ) | ~spl7_25),
% 2.00/0.63    inference(resolution,[],[f85,f232])).
% 2.00/0.63  fof(f232,plain,(
% 2.00/0.63    v1_relat_1(sK5) | ~spl7_25),
% 2.00/0.63    inference(avatar_component_clause,[],[f230])).
% 2.00/0.63  fof(f85,plain,(
% 2.00/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.00/0.63    inference(cnf_transformation,[],[f42])).
% 2.00/0.63  fof(f42,plain,(
% 2.00/0.63    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.00/0.63    inference(ennf_transformation,[],[f8])).
% 2.00/0.63  fof(f8,axiom,(
% 2.00/0.63    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.00/0.63  fof(f287,plain,(
% 2.00/0.63    ( ! [X0] : (k1_xboole_0 != k2_relat_1(k7_relat_1(sK5,X0)) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl7_25),
% 2.00/0.63    inference(resolution,[],[f244,f76])).
% 2.00/0.63  fof(f76,plain,(
% 2.00/0.63    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 2.00/0.63    inference(cnf_transformation,[],[f33])).
% 2.00/0.63  fof(f33,plain,(
% 2.00/0.63    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.00/0.63    inference(flattening,[],[f32])).
% 2.00/0.63  fof(f32,plain,(
% 2.00/0.63    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.00/0.63    inference(ennf_transformation,[],[f12])).
% 2.00/0.63  fof(f12,axiom,(
% 2.00/0.63    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 2.00/0.63  fof(f244,plain,(
% 2.00/0.63    ( ! [X1] : (v1_relat_1(k7_relat_1(sK5,X1))) ) | ~spl7_25),
% 2.00/0.63    inference(resolution,[],[f232,f83])).
% 2.00/0.63  fof(f83,plain,(
% 2.00/0.63    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 2.00/0.63    inference(cnf_transformation,[],[f40])).
% 2.00/0.63  fof(f40,plain,(
% 2.00/0.63    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.00/0.63    inference(ennf_transformation,[],[f6])).
% 2.00/0.63  fof(f6,axiom,(
% 2.00/0.63    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.00/0.63  fof(f911,plain,(
% 2.00/0.63    spl7_108 | ~spl7_24 | ~spl7_85),
% 2.00/0.63    inference(avatar_split_clause,[],[f905,f707,f225,f908])).
% 2.00/0.63  fof(f225,plain,(
% 2.00/0.63    spl7_24 <=> v1_relat_1(sK4)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 2.00/0.63  fof(f707,plain,(
% 2.00/0.63    spl7_85 <=> k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).
% 2.00/0.63  fof(f905,plain,(
% 2.00/0.63    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | (~spl7_24 | ~spl7_85)),
% 2.00/0.63    inference(trivial_inequality_removal,[],[f904])).
% 2.00/0.63  fof(f904,plain,(
% 2.00/0.63    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | (~spl7_24 | ~spl7_85)),
% 2.00/0.63    inference(superposition,[],[f901,f709])).
% 2.00/0.63  fof(f709,plain,(
% 2.00/0.63    k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0) | ~spl7_85),
% 2.00/0.63    inference(avatar_component_clause,[],[f707])).
% 2.00/0.63  fof(f901,plain,(
% 2.00/0.63    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK4,X0) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl7_24),
% 2.00/0.63    inference(superposition,[],[f276,f305])).
% 2.00/0.63  fof(f305,plain,(
% 2.00/0.63    ( ! [X0] : (k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0)) ) | ~spl7_24),
% 2.00/0.63    inference(resolution,[],[f85,f227])).
% 2.00/0.63  fof(f227,plain,(
% 2.00/0.63    v1_relat_1(sK4) | ~spl7_24),
% 2.00/0.63    inference(avatar_component_clause,[],[f225])).
% 2.00/0.63  fof(f276,plain,(
% 2.00/0.63    ( ! [X0] : (k1_xboole_0 != k2_relat_1(k7_relat_1(sK4,X0)) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl7_24),
% 2.00/0.63    inference(resolution,[],[f76,f236])).
% 2.00/0.63  fof(f236,plain,(
% 2.00/0.63    ( ! [X1] : (v1_relat_1(k7_relat_1(sK4,X1))) ) | ~spl7_24),
% 2.00/0.63    inference(resolution,[],[f227,f83])).
% 2.00/0.63  fof(f880,plain,(
% 2.00/0.63    spl7_104 | ~spl7_10 | ~spl7_9 | ~spl7_8 | ~spl7_82),
% 2.00/0.63    inference(avatar_split_clause,[],[f875,f662,f143,f148,f153,f877])).
% 2.00/0.63  fof(f662,plain,(
% 2.00/0.63    spl7_82 <=> ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).
% 2.00/0.63  fof(f875,plain,(
% 2.00/0.63    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl7_8 | ~spl7_82)),
% 2.00/0.63    inference(resolution,[],[f663,f145])).
% 2.00/0.63  fof(f145,plain,(
% 2.00/0.63    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl7_8),
% 2.00/0.63    inference(avatar_component_clause,[],[f143])).
% 2.00/0.63  fof(f663,plain,(
% 2.00/0.63    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))) ) | ~spl7_82),
% 2.00/0.63    inference(avatar_component_clause,[],[f662])).
% 2.00/0.63  fof(f820,plain,(
% 2.00/0.63    spl7_99 | ~spl7_10 | ~spl7_9 | ~spl7_8 | ~spl7_78),
% 2.00/0.63    inference(avatar_split_clause,[],[f815,f633,f143,f148,f153,f817])).
% 2.00/0.63  fof(f633,plain,(
% 2.00/0.63    spl7_78 <=> ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).
% 2.00/0.63  fof(f815,plain,(
% 2.00/0.63    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl7_8 | ~spl7_78)),
% 2.00/0.63    inference(resolution,[],[f634,f145])).
% 2.00/0.63  fof(f634,plain,(
% 2.00/0.63    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)) ) | ~spl7_78),
% 2.00/0.63    inference(avatar_component_clause,[],[f633])).
% 2.00/0.63  fof(f791,plain,(
% 2.00/0.63    spl7_95 | ~spl7_10 | ~spl7_9 | ~spl7_8 | ~spl7_72),
% 2.00/0.63    inference(avatar_split_clause,[],[f786,f596,f143,f148,f153,f788])).
% 2.00/0.63  fof(f596,plain,(
% 2.00/0.63    spl7_72 <=> ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).
% 2.00/0.63  fof(f786,plain,(
% 2.00/0.63    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl7_8 | ~spl7_72)),
% 2.00/0.63    inference(resolution,[],[f597,f145])).
% 2.00/0.63  fof(f597,plain,(
% 2.00/0.63    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))) ) | ~spl7_72),
% 2.00/0.63    inference(avatar_component_clause,[],[f596])).
% 2.00/0.63  fof(f751,plain,(
% 2.00/0.63    spl7_90 | ~spl7_25 | ~spl7_66 | ~spl7_68 | ~spl7_70),
% 2.00/0.63    inference(avatar_split_clause,[],[f750,f572,f551,f522,f230,f745])).
% 2.00/0.63  fof(f522,plain,(
% 2.00/0.63    spl7_66 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).
% 2.00/0.63  fof(f551,plain,(
% 2.00/0.63    spl7_68 <=> k1_xboole_0 = k7_relat_1(sK5,sK2)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).
% 2.00/0.63  fof(f572,plain,(
% 2.00/0.63    spl7_70 <=> r1_tarski(k1_xboole_0,sK2)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).
% 2.00/0.63  fof(f750,plain,(
% 2.00/0.63    k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0) | (~spl7_25 | ~spl7_66 | ~spl7_68 | ~spl7_70)),
% 2.00/0.63    inference(forward_demodulation,[],[f749,f524])).
% 2.00/0.63  fof(f524,plain,(
% 2.00/0.63    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | ~spl7_66),
% 2.00/0.63    inference(avatar_component_clause,[],[f522])).
% 2.00/0.63  fof(f749,plain,(
% 2.00/0.63    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0) | (~spl7_25 | ~spl7_68 | ~spl7_70)),
% 2.00/0.63    inference(forward_demodulation,[],[f736,f553])).
% 2.00/0.63  fof(f553,plain,(
% 2.00/0.63    k1_xboole_0 = k7_relat_1(sK5,sK2) | ~spl7_68),
% 2.00/0.63    inference(avatar_component_clause,[],[f551])).
% 2.00/0.63  fof(f736,plain,(
% 2.00/0.63    k9_relat_1(sK5,k1_xboole_0) = k9_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0) | (~spl7_25 | ~spl7_70)),
% 2.00/0.63    inference(resolution,[],[f358,f574])).
% 2.00/0.63  fof(f574,plain,(
% 2.00/0.63    r1_tarski(k1_xboole_0,sK2) | ~spl7_70),
% 2.00/0.63    inference(avatar_component_clause,[],[f572])).
% 2.00/0.63  fof(f358,plain,(
% 2.00/0.63    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k9_relat_1(k7_relat_1(sK5,X3),X2) = k9_relat_1(sK5,X2)) ) | ~spl7_25),
% 2.00/0.63    inference(resolution,[],[f78,f232])).
% 2.00/0.63  fof(f78,plain,(
% 2.00/0.63    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 2.00/0.63    inference(cnf_transformation,[],[f35])).
% 2.00/0.63  fof(f35,plain,(
% 2.00/0.63    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 2.00/0.63    inference(ennf_transformation,[],[f9])).
% 2.00/0.63  fof(f9,axiom,(
% 2.00/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 2.00/0.63  fof(f710,plain,(
% 2.00/0.63    spl7_85 | ~spl7_24 | ~spl7_62 | ~spl7_65 | ~spl7_66),
% 2.00/0.63    inference(avatar_split_clause,[],[f705,f522,f507,f483,f225,f707])).
% 2.00/0.63  fof(f483,plain,(
% 2.00/0.63    spl7_62 <=> k1_xboole_0 = k7_relat_1(sK4,sK6(sK2))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).
% 2.00/0.63  fof(f507,plain,(
% 2.00/0.63    spl7_65 <=> r1_tarski(k1_xboole_0,sK6(sK2))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).
% 2.00/0.63  fof(f705,plain,(
% 2.00/0.63    k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0) | (~spl7_24 | ~spl7_62 | ~spl7_65 | ~spl7_66)),
% 2.00/0.63    inference(forward_demodulation,[],[f704,f524])).
% 2.00/0.63  fof(f704,plain,(
% 2.00/0.63    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0) | (~spl7_24 | ~spl7_62 | ~spl7_65)),
% 2.00/0.63    inference(forward_demodulation,[],[f701,f485])).
% 2.00/0.63  fof(f485,plain,(
% 2.00/0.63    k1_xboole_0 = k7_relat_1(sK4,sK6(sK2)) | ~spl7_62),
% 2.00/0.63    inference(avatar_component_clause,[],[f483])).
% 2.00/0.63  fof(f701,plain,(
% 2.00/0.63    k9_relat_1(sK4,k1_xboole_0) = k9_relat_1(k7_relat_1(sK4,sK6(sK2)),k1_xboole_0) | (~spl7_24 | ~spl7_65)),
% 2.00/0.63    inference(resolution,[],[f357,f509])).
% 2.00/0.63  fof(f509,plain,(
% 2.00/0.63    r1_tarski(k1_xboole_0,sK6(sK2)) | ~spl7_65),
% 2.00/0.63    inference(avatar_component_clause,[],[f507])).
% 2.00/0.63  fof(f357,plain,(
% 2.00/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k9_relat_1(sK4,X0) = k9_relat_1(k7_relat_1(sK4,X1),X0)) ) | ~spl7_24),
% 2.00/0.63    inference(resolution,[],[f78,f227])).
% 2.00/0.63  fof(f664,plain,(
% 2.00/0.63    ~spl7_6 | ~spl7_12 | spl7_7 | ~spl7_13 | spl7_2 | spl7_82 | ~spl7_11 | ~spl7_57),
% 2.00/0.63    inference(avatar_split_clause,[],[f656,f456,f158,f662,f113,f168,f138,f163,f133])).
% 2.00/0.63  fof(f456,plain,(
% 2.00/0.63    spl7_57 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).
% 2.00/0.63  fof(f656,plain,(
% 2.00/0.63    ( ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl7_11 | ~spl7_57)),
% 2.00/0.63    inference(resolution,[],[f457,f160])).
% 2.00/0.63  fof(f160,plain,(
% 2.00/0.63    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl7_11),
% 2.00/0.63    inference(avatar_component_clause,[],[f158])).
% 2.00/0.63  fof(f457,plain,(
% 2.00/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl7_57),
% 2.00/0.63    inference(avatar_component_clause,[],[f456])).
% 2.00/0.63  fof(f635,plain,(
% 2.00/0.63    ~spl7_6 | ~spl7_12 | spl7_7 | ~spl7_13 | spl7_2 | spl7_78 | ~spl7_11 | ~spl7_54),
% 2.00/0.63    inference(avatar_split_clause,[],[f627,f440,f158,f633,f113,f168,f138,f163,f133])).
% 2.00/0.63  fof(f440,plain,(
% 2.00/0.63    spl7_54 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).
% 2.00/0.63  fof(f627,plain,(
% 2.00/0.63    ( ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl7_11 | ~spl7_54)),
% 2.00/0.63    inference(resolution,[],[f441,f160])).
% 2.00/0.63  fof(f441,plain,(
% 2.00/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl7_54),
% 2.00/0.63    inference(avatar_component_clause,[],[f440])).
% 2.00/0.63  fof(f598,plain,(
% 2.00/0.63    ~spl7_6 | ~spl7_12 | spl7_7 | ~spl7_13 | spl7_2 | spl7_72 | ~spl7_11 | ~spl7_50),
% 2.00/0.63    inference(avatar_split_clause,[],[f590,f420,f158,f596,f113,f168,f138,f163,f133])).
% 2.00/0.63  fof(f420,plain,(
% 2.00/0.63    spl7_50 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 2.00/0.63  fof(f590,plain,(
% 2.00/0.63    ( ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl7_11 | ~spl7_50)),
% 2.00/0.63    inference(resolution,[],[f421,f160])).
% 2.00/0.63  fof(f421,plain,(
% 2.00/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl7_50),
% 2.00/0.63    inference(avatar_component_clause,[],[f420])).
% 2.00/0.63  fof(f575,plain,(
% 2.00/0.63    spl7_70 | ~spl7_19 | ~spl7_25 | ~spl7_68),
% 2.00/0.63    inference(avatar_split_clause,[],[f570,f551,f230,f196,f572])).
% 2.00/0.63  fof(f196,plain,(
% 2.00/0.63    spl7_19 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 2.00/0.63  fof(f570,plain,(
% 2.00/0.63    r1_tarski(k1_xboole_0,sK2) | (~spl7_19 | ~spl7_25 | ~spl7_68)),
% 2.00/0.63    inference(forward_demodulation,[],[f562,f198])).
% 2.00/0.63  fof(f198,plain,(
% 2.00/0.63    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_19),
% 2.00/0.63    inference(avatar_component_clause,[],[f196])).
% 2.00/0.63  fof(f562,plain,(
% 2.00/0.63    r1_tarski(k1_relat_1(k1_xboole_0),sK2) | (~spl7_25 | ~spl7_68)),
% 2.00/0.63    inference(superposition,[],[f243,f553])).
% 2.00/0.63  fof(f243,plain,(
% 2.00/0.63    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),X0)) ) | ~spl7_25),
% 2.00/0.63    inference(resolution,[],[f232,f84])).
% 2.00/0.63  fof(f84,plain,(
% 2.00/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 2.00/0.63    inference(cnf_transformation,[],[f41])).
% 2.00/0.63  fof(f41,plain,(
% 2.00/0.63    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.00/0.63    inference(ennf_transformation,[],[f13])).
% 2.00/0.63  fof(f13,axiom,(
% 2.00/0.63    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 2.00/0.63  fof(f554,plain,(
% 2.00/0.63    spl7_68 | ~spl7_36 | ~spl7_61),
% 2.00/0.63    inference(avatar_split_clause,[],[f544,f478,f312,f551])).
% 2.00/0.63  fof(f312,plain,(
% 2.00/0.63    spl7_36 <=> r1_xboole_0(sK2,sK3)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 2.00/0.63  fof(f478,plain,(
% 2.00/0.63    spl7_61 <=> ! [X0] : (~r1_xboole_0(X0,sK3) | k1_xboole_0 = k7_relat_1(sK5,X0))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).
% 2.00/0.63  fof(f544,plain,(
% 2.00/0.63    k1_xboole_0 = k7_relat_1(sK5,sK2) | (~spl7_36 | ~spl7_61)),
% 2.00/0.63    inference(resolution,[],[f479,f314])).
% 2.00/0.63  fof(f314,plain,(
% 2.00/0.63    r1_xboole_0(sK2,sK3) | ~spl7_36),
% 2.00/0.63    inference(avatar_component_clause,[],[f312])).
% 2.00/0.63  fof(f479,plain,(
% 2.00/0.63    ( ! [X0] : (~r1_xboole_0(X0,sK3) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl7_61),
% 2.00/0.63    inference(avatar_component_clause,[],[f478])).
% 2.00/0.63  fof(f525,plain,(
% 2.00/0.63    spl7_66 | ~spl7_18 | ~spl7_19 | ~spl7_39),
% 2.00/0.63    inference(avatar_split_clause,[],[f520,f331,f196,f191,f522])).
% 2.00/0.63  fof(f191,plain,(
% 2.00/0.63    spl7_18 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 2.00/0.63  fof(f331,plain,(
% 2.00/0.63    spl7_39 <=> v1_relat_1(k1_xboole_0)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 2.00/0.63  fof(f520,plain,(
% 2.00/0.63    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | (~spl7_18 | ~spl7_19 | ~spl7_39)),
% 2.00/0.63    inference(forward_demodulation,[],[f519,f193])).
% 2.00/0.63  fof(f193,plain,(
% 2.00/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl7_18),
% 2.00/0.63    inference(avatar_component_clause,[],[f191])).
% 2.00/0.63  fof(f519,plain,(
% 2.00/0.63    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) | (~spl7_19 | ~spl7_39)),
% 2.00/0.63    inference(forward_demodulation,[],[f512,f198])).
% 2.00/0.63  fof(f512,plain,(
% 2.00/0.63    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) | ~spl7_39),
% 2.00/0.63    inference(resolution,[],[f332,f74])).
% 2.00/0.63  fof(f74,plain,(
% 2.00/0.63    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 2.00/0.63    inference(cnf_transformation,[],[f31])).
% 2.00/0.63  fof(f31,plain,(
% 2.00/0.63    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.00/0.63    inference(ennf_transformation,[],[f7])).
% 2.00/0.63  fof(f7,axiom,(
% 2.00/0.63    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 2.00/0.63  fof(f332,plain,(
% 2.00/0.63    v1_relat_1(k1_xboole_0) | ~spl7_39),
% 2.00/0.63    inference(avatar_component_clause,[],[f331])).
% 2.00/0.63  fof(f511,plain,(
% 2.00/0.63    spl7_39 | ~spl7_24 | ~spl7_62),
% 2.00/0.63    inference(avatar_split_clause,[],[f498,f483,f225,f331])).
% 2.00/0.63  fof(f498,plain,(
% 2.00/0.63    v1_relat_1(k1_xboole_0) | (~spl7_24 | ~spl7_62)),
% 2.00/0.63    inference(superposition,[],[f236,f485])).
% 2.00/0.63  fof(f510,plain,(
% 2.00/0.63    spl7_65 | ~spl7_19 | ~spl7_24 | ~spl7_62),
% 2.00/0.63    inference(avatar_split_clause,[],[f505,f483,f225,f196,f507])).
% 2.00/0.63  fof(f505,plain,(
% 2.00/0.63    r1_tarski(k1_xboole_0,sK6(sK2)) | (~spl7_19 | ~spl7_24 | ~spl7_62)),
% 2.00/0.63    inference(forward_demodulation,[],[f497,f198])).
% 2.00/0.63  fof(f497,plain,(
% 2.00/0.63    r1_tarski(k1_relat_1(k1_xboole_0),sK6(sK2)) | (~spl7_24 | ~spl7_62)),
% 2.00/0.63    inference(superposition,[],[f235,f485])).
% 2.00/0.63  fof(f235,plain,(
% 2.00/0.63    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0)) ) | ~spl7_24),
% 2.00/0.63    inference(resolution,[],[f227,f84])).
% 2.00/0.63  fof(f489,plain,(
% 2.00/0.63    k1_xboole_0 != sK4 | sK2 != k1_relat_1(sK4) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | v1_xboole_0(sK2) | ~v1_xboole_0(k1_xboole_0)),
% 2.00/0.63    introduced(theory_tautology_sat_conflict,[])).
% 2.00/0.63  fof(f486,plain,(
% 2.00/0.63    spl7_48 | spl7_62 | ~spl7_49),
% 2.00/0.63    inference(avatar_split_clause,[],[f481,f412,f483,f407])).
% 2.00/0.63  fof(f407,plain,(
% 2.00/0.63    spl7_48 <=> k1_xboole_0 = sK2),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 2.00/0.63  fof(f412,plain,(
% 2.00/0.63    spl7_49 <=> ! [X0] : (~r1_xboole_0(X0,sK2) | k1_xboole_0 = k7_relat_1(sK4,X0))),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).
% 2.00/0.63  fof(f481,plain,(
% 2.00/0.63    k1_xboole_0 = k7_relat_1(sK4,sK6(sK2)) | k1_xboole_0 = sK2 | ~spl7_49),
% 2.00/0.63    inference(resolution,[],[f413,f80])).
% 2.00/0.63  fof(f80,plain,(
% 2.00/0.63    ( ! [X0] : (r1_xboole_0(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 2.00/0.63    inference(cnf_transformation,[],[f37])).
% 2.00/0.63  fof(f37,plain,(
% 2.00/0.63    ! [X0] : (? [X1] : r1_xboole_0(X1,X0) | k1_xboole_0 = X0)),
% 2.00/0.63    inference(ennf_transformation,[],[f25])).
% 2.00/0.63  fof(f25,plain,(
% 2.00/0.63    ! [X0] : ~(! [X1] : ~r1_xboole_0(X1,X0) & k1_xboole_0 != X0)),
% 2.00/0.63    inference(pure_predicate_removal,[],[f17])).
% 2.00/0.63  fof(f17,axiom,(
% 2.00/0.63    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).
% 2.00/0.63  fof(f413,plain,(
% 2.00/0.63    ( ! [X0] : (~r1_xboole_0(X0,sK2) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl7_49),
% 2.00/0.63    inference(avatar_component_clause,[],[f412])).
% 2.00/0.63  fof(f480,plain,(
% 2.00/0.63    ~spl7_25 | spl7_61 | ~spl7_46),
% 2.00/0.63    inference(avatar_split_clause,[],[f465,f393,f478,f230])).
% 2.00/0.63  fof(f393,plain,(
% 2.00/0.63    spl7_46 <=> sK3 = k1_relat_1(sK5)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 2.00/0.63  fof(f465,plain,(
% 2.00/0.63    ( ! [X0] : (~r1_xboole_0(X0,sK3) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl7_46),
% 2.00/0.63    inference(superposition,[],[f77,f395])).
% 2.00/0.63  fof(f395,plain,(
% 2.00/0.63    sK3 = k1_relat_1(sK5) | ~spl7_46),
% 2.00/0.63    inference(avatar_component_clause,[],[f393])).
% 2.00/0.63  fof(f77,plain,(
% 2.00/0.63    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 2.00/0.63    inference(cnf_transformation,[],[f34])).
% 2.00/0.63  fof(f34,plain,(
% 2.00/0.63    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.00/0.63    inference(ennf_transformation,[],[f10])).
% 2.00/0.63  fof(f10,axiom,(
% 2.00/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 2.00/0.63  fof(f458,plain,(
% 2.00/0.63    spl7_1 | spl7_4 | spl7_57 | ~spl7_3),
% 2.00/0.63    inference(avatar_split_clause,[],[f451,f118,f456,f123,f108])).
% 2.00/0.63  fof(f451,plain,(
% 2.00/0.63    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0)))) ) | ~spl7_3),
% 2.00/0.63    inference(resolution,[],[f98,f120])).
% 2.00/0.63  fof(f120,plain,(
% 2.00/0.63    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl7_3),
% 2.00/0.63    inference(avatar_component_clause,[],[f118])).
% 2.00/0.63  fof(f98,plain,(
% 2.00/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 2.00/0.63    inference(cnf_transformation,[],[f53])).
% 2.00/0.63  fof(f53,plain,(
% 2.00/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.00/0.63    inference(flattening,[],[f52])).
% 2.00/0.63  fof(f52,plain,(
% 2.00/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.00/0.63    inference(ennf_transformation,[],[f22])).
% 2.00/0.63  fof(f22,axiom,(
% 2.00/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 2.00/0.63  fof(f442,plain,(
% 2.00/0.63    spl7_1 | spl7_4 | spl7_54 | ~spl7_3),
% 2.00/0.63    inference(avatar_split_clause,[],[f435,f118,f440,f123,f108])).
% 2.00/0.63  fof(f435,plain,(
% 2.00/0.63    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0)) ) | ~spl7_3),
% 2.00/0.63    inference(resolution,[],[f97,f120])).
% 2.00/0.63  fof(f97,plain,(
% 2.00/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 2.00/0.63    inference(cnf_transformation,[],[f53])).
% 2.00/0.63  fof(f422,plain,(
% 2.00/0.63    spl7_1 | spl7_4 | spl7_50 | ~spl7_3),
% 2.00/0.63    inference(avatar_split_clause,[],[f415,f118,f420,f123,f108])).
% 2.00/0.63  fof(f415,plain,(
% 2.00/0.63    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3))) ) | ~spl7_3),
% 2.00/0.63    inference(resolution,[],[f96,f120])).
% 2.00/0.63  fof(f96,plain,(
% 2.00/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 2.00/0.63    inference(cnf_transformation,[],[f53])).
% 2.00/0.63  fof(f414,plain,(
% 2.00/0.63    ~spl7_24 | spl7_49 | ~spl7_43),
% 2.00/0.63    inference(avatar_split_clause,[],[f399,f377,f412,f225])).
% 2.00/0.63  fof(f377,plain,(
% 2.00/0.63    spl7_43 <=> sK2 = k1_relat_1(sK4)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 2.00/0.63  fof(f399,plain,(
% 2.00/0.63    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~v1_relat_1(sK4) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl7_43),
% 2.00/0.63    inference(superposition,[],[f77,f379])).
% 2.00/0.63  fof(f379,plain,(
% 2.00/0.63    sK2 = k1_relat_1(sK4) | ~spl7_43),
% 2.00/0.63    inference(avatar_component_clause,[],[f377])).
% 2.00/0.63  fof(f410,plain,(
% 2.00/0.63    ~spl7_48 | spl7_29 | ~spl7_43),
% 2.00/0.63    inference(avatar_split_clause,[],[f398,f377,f257,f407])).
% 2.00/0.63  fof(f257,plain,(
% 2.00/0.63    spl7_29 <=> k1_xboole_0 = k1_relat_1(sK4)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 2.00/0.63  fof(f398,plain,(
% 2.00/0.63    k1_xboole_0 != sK2 | (spl7_29 | ~spl7_43)),
% 2.00/0.63    inference(superposition,[],[f259,f379])).
% 2.00/0.63  fof(f259,plain,(
% 2.00/0.63    k1_xboole_0 != k1_relat_1(sK4) | spl7_29),
% 2.00/0.63    inference(avatar_component_clause,[],[f257])).
% 2.00/0.63  fof(f396,plain,(
% 2.00/0.63    ~spl7_25 | spl7_46 | ~spl7_35 | ~spl7_42),
% 2.00/0.63    inference(avatar_split_clause,[],[f391,f371,f300,f393,f230])).
% 2.00/0.63  fof(f300,plain,(
% 2.00/0.63    spl7_35 <=> v4_relat_1(sK5,sK3)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 2.00/0.63  fof(f371,plain,(
% 2.00/0.63    spl7_42 <=> v1_partfun1(sK5,sK3)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 2.00/0.63  fof(f391,plain,(
% 2.00/0.63    ~v4_relat_1(sK5,sK3) | sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5) | ~spl7_42),
% 2.00/0.63    inference(resolution,[],[f373,f89])).
% 2.00/0.63  fof(f89,plain,(
% 2.00/0.63    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 2.00/0.63    inference(cnf_transformation,[],[f46])).
% 2.00/0.63  fof(f46,plain,(
% 2.00/0.63    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.00/0.63    inference(flattening,[],[f45])).
% 2.00/0.63  fof(f45,plain,(
% 2.00/0.63    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.00/0.63    inference(ennf_transformation,[],[f19])).
% 2.00/0.63  fof(f19,axiom,(
% 2.00/0.63    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 2.00/0.63  fof(f373,plain,(
% 2.00/0.63    v1_partfun1(sK5,sK3) | ~spl7_42),
% 2.00/0.63    inference(avatar_component_clause,[],[f371])).
% 2.00/0.63  fof(f390,plain,(
% 2.00/0.63    spl7_45 | ~spl7_13 | ~spl7_11),
% 2.00/0.63    inference(avatar_split_clause,[],[f382,f158,f168,f388])).
% 2.00/0.63  fof(f382,plain,(
% 2.00/0.63    ( ! [X1] : (~v1_funct_1(sK5) | k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl7_11),
% 2.00/0.63    inference(resolution,[],[f95,f160])).
% 2.00/0.63  fof(f95,plain,(
% 2.00/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 2.00/0.63    inference(cnf_transformation,[],[f51])).
% 2.00/0.63  fof(f51,plain,(
% 2.00/0.63    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.00/0.63    inference(flattening,[],[f50])).
% 2.00/0.63  fof(f50,plain,(
% 2.00/0.63    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.00/0.63    inference(ennf_transformation,[],[f20])).
% 2.00/0.63  fof(f20,axiom,(
% 2.00/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.00/0.63  fof(f386,plain,(
% 2.00/0.63    spl7_44 | ~spl7_10 | ~spl7_8),
% 2.00/0.63    inference(avatar_split_clause,[],[f381,f143,f153,f384])).
% 2.00/0.63  fof(f381,plain,(
% 2.00/0.63    ( ! [X0] : (~v1_funct_1(sK4) | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl7_8),
% 2.00/0.63    inference(resolution,[],[f95,f145])).
% 2.00/0.63  fof(f380,plain,(
% 2.00/0.63    ~spl7_24 | spl7_43 | ~spl7_34 | ~spl7_41),
% 2.00/0.63    inference(avatar_split_clause,[],[f375,f366,f295,f377,f225])).
% 2.00/0.63  fof(f295,plain,(
% 2.00/0.63    spl7_34 <=> v4_relat_1(sK4,sK2)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 2.00/0.63  fof(f366,plain,(
% 2.00/0.63    spl7_41 <=> v1_partfun1(sK4,sK2)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 2.00/0.63  fof(f375,plain,(
% 2.00/0.63    ~v4_relat_1(sK4,sK2) | sK2 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl7_41),
% 2.00/0.63    inference(resolution,[],[f368,f89])).
% 2.00/0.63  fof(f368,plain,(
% 2.00/0.63    v1_partfun1(sK4,sK2) | ~spl7_41),
% 2.00/0.63    inference(avatar_component_clause,[],[f366])).
% 2.00/0.63  fof(f374,plain,(
% 2.00/0.63    spl7_42 | ~spl7_12 | ~spl7_13 | spl7_2 | ~spl7_11),
% 2.00/0.63    inference(avatar_split_clause,[],[f364,f158,f113,f168,f163,f371])).
% 2.00/0.63  fof(f364,plain,(
% 2.00/0.63    v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3) | ~spl7_11),
% 2.00/0.63    inference(resolution,[],[f82,f160])).
% 2.00/0.63  fof(f82,plain,(
% 2.00/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 2.00/0.63    inference(cnf_transformation,[],[f39])).
% 2.00/0.63  fof(f39,plain,(
% 2.00/0.63    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.00/0.63    inference(flattening,[],[f38])).
% 2.00/0.63  fof(f38,plain,(
% 2.00/0.63    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.00/0.63    inference(ennf_transformation,[],[f18])).
% 2.00/0.63  fof(f18,axiom,(
% 2.00/0.63    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 2.00/0.63  fof(f369,plain,(
% 2.00/0.63    spl7_41 | ~spl7_9 | ~spl7_10 | spl7_2 | ~spl7_8),
% 2.00/0.63    inference(avatar_split_clause,[],[f363,f143,f113,f153,f148,f366])).
% 2.00/0.63  fof(f363,plain,(
% 2.00/0.63    v1_xboole_0(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2) | ~spl7_8),
% 2.00/0.63    inference(resolution,[],[f82,f145])).
% 2.00/0.63  fof(f322,plain,(
% 2.00/0.63    spl7_37 | ~spl7_36),
% 2.00/0.63    inference(avatar_split_clause,[],[f317,f312,f319])).
% 2.00/0.63  fof(f317,plain,(
% 2.00/0.63    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl7_36),
% 2.00/0.63    inference(resolution,[],[f314,f99])).
% 2.00/0.63  fof(f99,plain,(
% 2.00/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.00/0.63    inference(definition_unfolding,[],[f91,f81])).
% 2.00/0.63  fof(f91,plain,(
% 2.00/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.00/0.63    inference(cnf_transformation,[],[f1])).
% 2.00/0.63  fof(f1,axiom,(
% 2.00/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.00/0.63  fof(f315,plain,(
% 2.00/0.63    spl7_4 | spl7_36 | spl7_7 | ~spl7_5),
% 2.00/0.63    inference(avatar_split_clause,[],[f310,f128,f138,f312,f123])).
% 2.00/0.63  fof(f128,plain,(
% 2.00/0.63    spl7_5 <=> r1_subset_1(sK2,sK3)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.00/0.63  fof(f310,plain,(
% 2.00/0.63    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | ~spl7_5),
% 2.00/0.63    inference(resolution,[],[f87,f130])).
% 2.00/0.63  fof(f130,plain,(
% 2.00/0.63    r1_subset_1(sK2,sK3) | ~spl7_5),
% 2.00/0.63    inference(avatar_component_clause,[],[f128])).
% 2.00/0.63  fof(f87,plain,(
% 2.00/0.63    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 2.00/0.63    inference(cnf_transformation,[],[f44])).
% 2.00/0.63  fof(f44,plain,(
% 2.00/0.63    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.00/0.63    inference(flattening,[],[f43])).
% 2.00/0.63  fof(f43,plain,(
% 2.00/0.63    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.00/0.63    inference(ennf_transformation,[],[f14])).
% 2.00/0.63  fof(f14,axiom,(
% 2.00/0.63    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 2.00/0.63  fof(f303,plain,(
% 2.00/0.63    spl7_35 | ~spl7_11),
% 2.00/0.63    inference(avatar_split_clause,[],[f293,f158,f300])).
% 2.00/0.63  fof(f293,plain,(
% 2.00/0.63    v4_relat_1(sK5,sK3) | ~spl7_11),
% 2.00/0.63    inference(resolution,[],[f94,f160])).
% 2.00/0.63  fof(f94,plain,(
% 2.00/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.00/0.63    inference(cnf_transformation,[],[f49])).
% 2.00/0.63  fof(f49,plain,(
% 2.00/0.63    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.63    inference(ennf_transformation,[],[f26])).
% 2.00/0.63  fof(f26,plain,(
% 2.00/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.00/0.63    inference(pure_predicate_removal,[],[f16])).
% 2.00/0.63  fof(f16,axiom,(
% 2.00/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.00/0.63  fof(f298,plain,(
% 2.00/0.63    spl7_34 | ~spl7_8),
% 2.00/0.63    inference(avatar_split_clause,[],[f292,f143,f295])).
% 2.00/0.63  fof(f292,plain,(
% 2.00/0.63    v4_relat_1(sK4,sK2) | ~spl7_8),
% 2.00/0.63    inference(resolution,[],[f94,f145])).
% 2.00/0.63  fof(f260,plain,(
% 2.00/0.63    spl7_28 | ~spl7_29 | ~spl7_24),
% 2.00/0.63    inference(avatar_split_clause,[],[f250,f225,f257,f253])).
% 2.00/0.63  fof(f253,plain,(
% 2.00/0.63    spl7_28 <=> k1_xboole_0 = sK4),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 2.00/0.63  fof(f250,plain,(
% 2.00/0.63    k1_xboole_0 != k1_relat_1(sK4) | k1_xboole_0 = sK4 | ~spl7_24),
% 2.00/0.63    inference(resolution,[],[f75,f227])).
% 2.00/0.63  fof(f75,plain,(
% 2.00/0.63    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 2.00/0.63    inference(cnf_transformation,[],[f33])).
% 2.00/0.63  fof(f233,plain,(
% 2.00/0.63    spl7_25 | ~spl7_11),
% 2.00/0.63    inference(avatar_split_clause,[],[f223,f158,f230])).
% 2.00/0.63  fof(f223,plain,(
% 2.00/0.63    v1_relat_1(sK5) | ~spl7_11),
% 2.00/0.63    inference(resolution,[],[f93,f160])).
% 2.00/0.63  fof(f93,plain,(
% 2.00/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.00/0.63    inference(cnf_transformation,[],[f48])).
% 2.00/0.63  fof(f48,plain,(
% 2.00/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.63    inference(ennf_transformation,[],[f15])).
% 2.00/0.63  fof(f15,axiom,(
% 2.00/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.00/0.63  fof(f228,plain,(
% 2.00/0.63    spl7_24 | ~spl7_8),
% 2.00/0.63    inference(avatar_split_clause,[],[f222,f143,f225])).
% 2.00/0.63  fof(f222,plain,(
% 2.00/0.63    v1_relat_1(sK4) | ~spl7_8),
% 2.00/0.63    inference(resolution,[],[f93,f145])).
% 2.00/0.63  fof(f199,plain,(
% 2.00/0.63    spl7_19),
% 2.00/0.63    inference(avatar_split_clause,[],[f69,f196])).
% 2.00/0.63  fof(f69,plain,(
% 2.00/0.63    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.00/0.63    inference(cnf_transformation,[],[f11])).
% 2.00/0.63  fof(f11,axiom,(
% 2.00/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 2.00/0.63  fof(f194,plain,(
% 2.00/0.63    spl7_18),
% 2.00/0.63    inference(avatar_split_clause,[],[f70,f191])).
% 2.00/0.63  fof(f70,plain,(
% 2.00/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.00/0.63    inference(cnf_transformation,[],[f11])).
% 2.00/0.63  fof(f189,plain,(
% 2.00/0.63    spl7_17),
% 2.00/0.63    inference(avatar_split_clause,[],[f68,f186])).
% 2.00/0.63  fof(f186,plain,(
% 2.00/0.63    spl7_17 <=> v1_xboole_0(k1_xboole_0)),
% 2.00/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 2.00/0.63  fof(f68,plain,(
% 2.00/0.63    v1_xboole_0(k1_xboole_0)),
% 2.00/0.63    inference(cnf_transformation,[],[f2])).
% 2.00/0.63  fof(f2,axiom,(
% 2.00/0.63    v1_xboole_0(k1_xboole_0)),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.00/0.63  fof(f184,plain,(
% 2.00/0.63    ~spl7_14 | ~spl7_15 | ~spl7_16),
% 2.00/0.63    inference(avatar_split_clause,[],[f54,f181,f177,f173])).
% 2.00/0.63  fof(f54,plain,(
% 2.00/0.63    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 2.00/0.63    inference(cnf_transformation,[],[f28])).
% 2.00/0.63  fof(f28,plain,(
% 2.00/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.00/0.63    inference(flattening,[],[f27])).
% 2.00/0.63  fof(f27,plain,(
% 2.00/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.00/0.63    inference(ennf_transformation,[],[f24])).
% 2.00/0.63  fof(f24,negated_conjecture,(
% 2.00/0.63    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 2.00/0.63    inference(negated_conjecture,[],[f23])).
% 2.00/0.63  fof(f23,conjecture,(
% 2.00/0.63    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).
% 2.00/0.63  fof(f171,plain,(
% 2.00/0.63    spl7_13),
% 2.00/0.63    inference(avatar_split_clause,[],[f55,f168])).
% 2.00/0.63  fof(f55,plain,(
% 2.00/0.63    v1_funct_1(sK5)),
% 2.00/0.63    inference(cnf_transformation,[],[f28])).
% 2.00/0.63  fof(f166,plain,(
% 2.00/0.63    spl7_12),
% 2.00/0.63    inference(avatar_split_clause,[],[f56,f163])).
% 2.00/0.63  fof(f56,plain,(
% 2.00/0.63    v1_funct_2(sK5,sK3,sK1)),
% 2.00/0.63    inference(cnf_transformation,[],[f28])).
% 2.00/0.63  fof(f161,plain,(
% 2.00/0.63    spl7_11),
% 2.00/0.63    inference(avatar_split_clause,[],[f57,f158])).
% 2.00/0.63  fof(f57,plain,(
% 2.00/0.63    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.00/0.63    inference(cnf_transformation,[],[f28])).
% 2.00/0.63  fof(f156,plain,(
% 2.00/0.63    spl7_10),
% 2.00/0.63    inference(avatar_split_clause,[],[f58,f153])).
% 2.00/0.63  fof(f58,plain,(
% 2.00/0.63    v1_funct_1(sK4)),
% 2.00/0.63    inference(cnf_transformation,[],[f28])).
% 2.00/0.63  fof(f151,plain,(
% 2.00/0.63    spl7_9),
% 2.00/0.63    inference(avatar_split_clause,[],[f59,f148])).
% 2.00/0.63  fof(f59,plain,(
% 2.00/0.63    v1_funct_2(sK4,sK2,sK1)),
% 2.00/0.63    inference(cnf_transformation,[],[f28])).
% 2.00/0.63  fof(f146,plain,(
% 2.00/0.63    spl7_8),
% 2.00/0.63    inference(avatar_split_clause,[],[f60,f143])).
% 2.00/0.63  fof(f60,plain,(
% 2.00/0.63    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.00/0.63    inference(cnf_transformation,[],[f28])).
% 2.00/0.63  fof(f141,plain,(
% 2.00/0.63    ~spl7_7),
% 2.00/0.63    inference(avatar_split_clause,[],[f61,f138])).
% 2.00/0.63  fof(f61,plain,(
% 2.00/0.63    ~v1_xboole_0(sK3)),
% 2.00/0.63    inference(cnf_transformation,[],[f28])).
% 2.00/0.63  fof(f136,plain,(
% 2.00/0.63    spl7_6),
% 2.00/0.63    inference(avatar_split_clause,[],[f62,f133])).
% 2.00/0.63  fof(f62,plain,(
% 2.00/0.63    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.00/0.63    inference(cnf_transformation,[],[f28])).
% 2.00/0.63  fof(f131,plain,(
% 2.00/0.63    spl7_5),
% 2.00/0.63    inference(avatar_split_clause,[],[f63,f128])).
% 2.00/0.63  fof(f63,plain,(
% 2.00/0.63    r1_subset_1(sK2,sK3)),
% 2.00/0.63    inference(cnf_transformation,[],[f28])).
% 2.00/0.63  fof(f126,plain,(
% 2.00/0.63    ~spl7_4),
% 2.00/0.63    inference(avatar_split_clause,[],[f64,f123])).
% 2.00/0.63  fof(f64,plain,(
% 2.00/0.63    ~v1_xboole_0(sK2)),
% 2.00/0.63    inference(cnf_transformation,[],[f28])).
% 2.00/0.63  fof(f121,plain,(
% 2.00/0.63    spl7_3),
% 2.00/0.63    inference(avatar_split_clause,[],[f65,f118])).
% 2.00/0.63  fof(f65,plain,(
% 2.00/0.63    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.00/0.63    inference(cnf_transformation,[],[f28])).
% 2.00/0.63  fof(f116,plain,(
% 2.00/0.63    ~spl7_2),
% 2.00/0.63    inference(avatar_split_clause,[],[f66,f113])).
% 2.00/0.63  fof(f66,plain,(
% 2.00/0.63    ~v1_xboole_0(sK1)),
% 2.00/0.63    inference(cnf_transformation,[],[f28])).
% 2.00/0.63  fof(f111,plain,(
% 2.00/0.63    ~spl7_1),
% 2.00/0.63    inference(avatar_split_clause,[],[f67,f108])).
% 2.00/0.63  fof(f67,plain,(
% 2.00/0.63    ~v1_xboole_0(sK0)),
% 2.00/0.63    inference(cnf_transformation,[],[f28])).
% 2.00/0.63  % SZS output end Proof for theBenchmark
% 2.00/0.63  % (25176)------------------------------
% 2.00/0.63  % (25176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.63  % (25176)Termination reason: Refutation
% 2.00/0.63  
% 2.00/0.63  % (25176)Memory used [KB]: 11897
% 2.00/0.63  % (25176)Time elapsed: 0.202 s
% 2.00/0.63  % (25176)------------------------------
% 2.00/0.63  % (25176)------------------------------
% 2.00/0.63  % (25159)Success in time 0.266 s
%------------------------------------------------------------------------------
