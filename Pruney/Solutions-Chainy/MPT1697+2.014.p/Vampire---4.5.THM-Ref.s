%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:28 EST 2020

% Result     : Theorem 1.99s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  299 ( 670 expanded)
%              Number of leaves         :   74 ( 327 expanded)
%              Depth                    :   14
%              Number of atoms          : 1470 (3174 expanded)
%              Number of equality atoms :  182 ( 466 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1675,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f112,f117,f122,f127,f132,f137,f142,f147,f152,f157,f162,f167,f180,f190,f219,f224,f237,f242,f284,f289,f302,f309,f363,f368,f374,f380,f384,f390,f414,f422,f442,f458,f486,f508,f509,f537,f539,f540,f552,f622,f639,f667,f677,f698,f754,f808,f878,f907,f967,f1578,f1586,f1672,f1674])).

fof(f1674,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | sK4 != k7_relat_1(sK4,k1_relat_1(sK4))
    | k1_xboole_0 != sK4
    | k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1672,plain,
    ( ~ spl7_92
    | ~ spl7_6
    | spl7_16
    | ~ spl7_36
    | ~ spl7_45
    | ~ spl7_46
    | ~ spl7_97 ),
    inference(avatar_split_clause,[],[f1671,f797,f382,f378,f306,f177,f129,f751])).

fof(f751,plain,
    ( spl7_92
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f129,plain,
    ( spl7_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f177,plain,
    ( spl7_16
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f306,plain,
    ( spl7_36
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f378,plain,
    ( spl7_45
  <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f382,plain,
    ( spl7_46
  <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f797,plain,
    ( spl7_97
  <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).

fof(f1671,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_6
    | spl7_16
    | ~ spl7_36
    | ~ spl7_45
    | ~ spl7_46
    | ~ spl7_97 ),
    inference(forward_demodulation,[],[f1670,f799])).

fof(f799,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl7_97 ),
    inference(avatar_component_clause,[],[f797])).

fof(f1670,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ spl7_6
    | spl7_16
    | ~ spl7_36
    | ~ spl7_45
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f1669,f379])).

fof(f379,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f378])).

fof(f1669,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl7_6
    | spl7_16
    | ~ spl7_36
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f1668,f308])).

fof(f308,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f306])).

fof(f1668,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl7_6
    | spl7_16
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f1667,f334])).

fof(f334,plain,
    ( ! [X1] : k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))
    | ~ spl7_6 ),
    inference(resolution,[],[f97,f131])).

fof(f131,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f88,f77])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f1667,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl7_16
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f179,f383])).

fof(f383,plain,
    ( ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f382])).

fof(f179,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f177])).

fof(f1586,plain,
    ( spl7_14
    | spl7_1
    | ~ spl7_108
    | ~ spl7_104
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
    | ~ spl7_45
    | ~ spl7_46
    | ~ spl7_92
    | ~ spl7_97
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f1585,f964,f797,f751,f382,f378,f306,f129,f109,f119,f114,f134,f129,f149,f144,f139,f164,f159,f154,f875,f904,f104,f169])).

fof(f169,plain,
    ( spl7_14
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f104,plain,
    ( spl7_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f904,plain,
    ( spl7_108
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f875,plain,
    ( spl7_104
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f154,plain,
    ( spl7_11
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f159,plain,
    ( spl7_12
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f164,plain,
    ( spl7_13
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f139,plain,
    ( spl7_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f144,plain,
    ( spl7_9
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f149,plain,
    ( spl7_10
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f134,plain,
    ( spl7_7
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f114,plain,
    ( spl7_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f119,plain,
    ( spl7_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f109,plain,
    ( spl7_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f964,plain,
    ( spl7_113
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).

fof(f1585,plain,
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
    | ~ spl7_45
    | ~ spl7_46
    | ~ spl7_92
    | ~ spl7_97
    | ~ spl7_113 ),
    inference(trivial_inequality_removal,[],[f1584])).

fof(f1584,plain,
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
    | ~ spl7_45
    | ~ spl7_46
    | ~ spl7_92
    | ~ spl7_97
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1583,f753])).

fof(f753,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_92 ),
    inference(avatar_component_clause,[],[f751])).

fof(f1583,plain,
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
    | ~ spl7_45
    | ~ spl7_46
    | ~ spl7_97
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1582,f799])).

fof(f1582,plain,
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
    | ~ spl7_45
    | ~ spl7_46
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1581,f379])).

fof(f1581,plain,
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
    | ~ spl7_46
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1580,f308])).

fof(f1580,plain,
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
    | ~ spl7_46
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1579,f334])).

fof(f1579,plain,
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
    | ~ spl7_46
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1554,f383])).

fof(f1554,plain,
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
    | ~ spl7_113 ),
    inference(resolution,[],[f966,f100])).

fof(f100,plain,(
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
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f28])).

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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f966,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl7_113 ),
    inference(avatar_component_clause,[],[f964])).

fof(f1578,plain,
    ( spl7_15
    | spl7_1
    | ~ spl7_108
    | ~ spl7_104
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
    | ~ spl7_45
    | ~ spl7_46
    | ~ spl7_92
    | ~ spl7_97
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f1577,f964,f797,f751,f382,f378,f306,f129,f109,f119,f114,f134,f129,f149,f144,f139,f164,f159,f154,f875,f904,f104,f173])).

fof(f173,plain,
    ( spl7_15
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f1577,plain,
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
    | ~ spl7_45
    | ~ spl7_46
    | ~ spl7_92
    | ~ spl7_97
    | ~ spl7_113 ),
    inference(trivial_inequality_removal,[],[f1576])).

fof(f1576,plain,
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
    | ~ spl7_45
    | ~ spl7_46
    | ~ spl7_92
    | ~ spl7_97
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1575,f753])).

fof(f1575,plain,
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
    | ~ spl7_45
    | ~ spl7_46
    | ~ spl7_97
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1574,f799])).

fof(f1574,plain,
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
    | ~ spl7_45
    | ~ spl7_46
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1573,f379])).

fof(f1573,plain,
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
    | ~ spl7_46
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1572,f308])).

fof(f1572,plain,
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
    | ~ spl7_46
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1571,f334])).

fof(f1571,plain,
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
    | ~ spl7_46
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1553,f383])).

fof(f1553,plain,
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
    | ~ spl7_113 ),
    inference(resolution,[],[f966,f101])).

fof(f101,plain,(
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
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f967,plain,
    ( spl7_113
    | ~ spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_89 ),
    inference(avatar_split_clause,[],[f962,f696,f139,f144,f149,f964])).

fof(f696,plain,
    ( spl7_89
  <=> ! [X1] :
        ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f962,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl7_8
    | ~ spl7_89 ),
    inference(resolution,[],[f697,f141])).

fof(f141,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f697,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) )
    | ~ spl7_89 ),
    inference(avatar_component_clause,[],[f696])).

fof(f907,plain,
    ( spl7_108
    | ~ spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_85 ),
    inference(avatar_split_clause,[],[f902,f675,f139,f144,f149,f904])).

fof(f675,plain,
    ( spl7_85
  <=> ! [X1] :
        ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f902,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl7_8
    | ~ spl7_85 ),
    inference(resolution,[],[f676,f141])).

fof(f676,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) )
    | ~ spl7_85 ),
    inference(avatar_component_clause,[],[f675])).

fof(f878,plain,
    ( spl7_104
    | ~ spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_75 ),
    inference(avatar_split_clause,[],[f873,f620,f139,f144,f149,f875])).

fof(f620,plain,
    ( spl7_75
  <=> ! [X1] :
        ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f873,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl7_8
    | ~ spl7_75 ),
    inference(resolution,[],[f621,f141])).

fof(f621,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) )
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f620])).

fof(f808,plain,
    ( spl7_97
    | ~ spl7_24
    | ~ spl7_70
    | ~ spl7_78
    | ~ spl7_83 ),
    inference(avatar_split_clause,[],[f807,f664,f636,f549,f221,f797])).

fof(f221,plain,
    ( spl7_24
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f549,plain,
    ( spl7_70
  <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f636,plain,
    ( spl7_78
  <=> k1_xboole_0 = k7_relat_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f664,plain,
    ( spl7_83
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f807,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_70
    | ~ spl7_78
    | ~ spl7_83 ),
    inference(forward_demodulation,[],[f806,f551])).

fof(f551,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f549])).

fof(f806,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_78
    | ~ spl7_83 ),
    inference(forward_demodulation,[],[f780,f638])).

fof(f638,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f636])).

fof(f780,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_83 ),
    inference(resolution,[],[f345,f666])).

fof(f666,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl7_83 ),
    inference(avatar_component_clause,[],[f664])).

fof(f345,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k7_relat_1(sK5,X2) = k7_relat_1(k7_relat_1(sK5,X3),X2) )
    | ~ spl7_24 ),
    inference(resolution,[],[f87,f223])).

fof(f223,plain,
    ( v1_relat_1(sK5)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f221])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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

fof(f754,plain,
    ( spl7_92
    | ~ spl7_23
    | ~ spl7_65
    | ~ spl7_67
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f749,f549,f522,f505,f216,f751])).

fof(f216,plain,
    ( spl7_23
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f505,plain,
    ( spl7_65
  <=> k1_xboole_0 = k7_relat_1(sK4,sK6(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f522,plain,
    ( spl7_67
  <=> r1_tarski(k1_xboole_0,sK6(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f749,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_23
    | ~ spl7_65
    | ~ spl7_67
    | ~ spl7_70 ),
    inference(forward_demodulation,[],[f748,f551])).

fof(f748,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl7_23
    | ~ spl7_65
    | ~ spl7_67 ),
    inference(forward_demodulation,[],[f736,f507])).

fof(f507,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK6(sK2))
    | ~ spl7_65 ),
    inference(avatar_component_clause,[],[f505])).

fof(f736,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k7_relat_1(sK4,sK6(sK2)),k1_xboole_0)
    | ~ spl7_23
    | ~ spl7_67 ),
    inference(resolution,[],[f344,f524])).

fof(f524,plain,
    ( r1_tarski(k1_xboole_0,sK6(sK2))
    | ~ spl7_67 ),
    inference(avatar_component_clause,[],[f522])).

fof(f344,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK4,X0) = k7_relat_1(k7_relat_1(sK4,X1),X0) )
    | ~ spl7_23 ),
    inference(resolution,[],[f87,f218])).

fof(f218,plain,
    ( v1_relat_1(sK4)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f216])).

fof(f698,plain,
    ( ~ spl7_6
    | ~ spl7_12
    | spl7_7
    | ~ spl7_13
    | spl7_2
    | spl7_89
    | ~ spl7_11
    | ~ spl7_59 ),
    inference(avatar_split_clause,[],[f690,f456,f154,f696,f109,f164,f134,f159,f129])).

fof(f456,plain,
    ( spl7_59
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
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f690,plain,
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
    | ~ spl7_59 ),
    inference(resolution,[],[f457,f156])).

fof(f156,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f154])).

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
    | ~ spl7_59 ),
    inference(avatar_component_clause,[],[f456])).

fof(f677,plain,
    ( ~ spl7_6
    | ~ spl7_12
    | spl7_7
    | ~ spl7_13
    | spl7_2
    | spl7_85
    | ~ spl7_11
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f669,f440,f154,f675,f109,f164,f134,f159,f129])).

fof(f440,plain,
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

fof(f669,plain,
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
    | ~ spl7_56 ),
    inference(resolution,[],[f441,f156])).

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
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f440])).

fof(f667,plain,
    ( spl7_83
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_78 ),
    inference(avatar_split_clause,[],[f662,f636,f221,f187,f664])).

fof(f187,plain,
    ( spl7_18
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f662,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_78 ),
    inference(forward_demodulation,[],[f660,f189])).

fof(f189,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f187])).

fof(f660,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK2)
    | ~ spl7_24
    | ~ spl7_78 ),
    inference(superposition,[],[f244,f638])).

fof(f244,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),X0)
    | ~ spl7_24 ),
    inference(resolution,[],[f223,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f639,plain,
    ( spl7_78
    | ~ spl7_35
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f634,f484,f299,f636])).

fof(f299,plain,
    ( spl7_35
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f484,plain,
    ( spl7_64
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f634,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl7_35
    | ~ spl7_64 ),
    inference(resolution,[],[f485,f301])).

fof(f301,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f299])).

fof(f485,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f484])).

fof(f622,plain,
    ( ~ spl7_6
    | ~ spl7_12
    | spl7_7
    | ~ spl7_13
    | spl7_2
    | spl7_75
    | ~ spl7_11
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f614,f420,f154,f620,f109,f164,f134,f159,f129])).

fof(f420,plain,
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

fof(f614,plain,
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
    inference(resolution,[],[f421,f156])).

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
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f420])).

fof(f552,plain,
    ( spl7_70
    | ~ spl7_18
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f547,f316,f187,f549])).

fof(f316,plain,
    ( spl7_38
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f547,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_18
    | ~ spl7_38 ),
    inference(forward_demodulation,[],[f545,f189])).

fof(f545,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl7_38 ),
    inference(resolution,[],[f317,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f317,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f316])).

fof(f540,plain,
    ( ~ spl7_50
    | spl7_26
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f393,f371,f234,f407])).

fof(f407,plain,
    ( spl7_50
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f234,plain,
    ( spl7_26
  <=> k1_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f371,plain,
    ( spl7_44
  <=> sK2 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f393,plain,
    ( k1_xboole_0 != sK2
    | spl7_26
    | ~ spl7_44 ),
    inference(superposition,[],[f236,f373])).

fof(f373,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f371])).

fof(f236,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | spl7_26 ),
    inference(avatar_component_clause,[],[f234])).

fof(f539,plain,
    ( spl7_67
    | ~ spl7_18
    | ~ spl7_23
    | ~ spl7_65 ),
    inference(avatar_split_clause,[],[f538,f505,f216,f187,f522])).

fof(f538,plain,
    ( r1_tarski(k1_xboole_0,sK6(sK2))
    | ~ spl7_18
    | ~ spl7_23
    | ~ spl7_65 ),
    inference(forward_demodulation,[],[f518,f189])).

fof(f518,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK6(sK2))
    | ~ spl7_23
    | ~ spl7_65 ),
    inference(superposition,[],[f226,f507])).

fof(f226,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0)
    | ~ spl7_23 ),
    inference(resolution,[],[f218,f80])).

fof(f537,plain,
    ( spl7_38
    | ~ spl7_23
    | ~ spl7_65 ),
    inference(avatar_split_clause,[],[f519,f505,f216,f316])).

fof(f519,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_23
    | ~ spl7_65 ),
    inference(superposition,[],[f228,f507])).

fof(f228,plain,
    ( ! [X1] : v1_relat_1(k7_relat_1(sK4,X1))
    | ~ spl7_23 ),
    inference(resolution,[],[f218,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f509,plain,
    ( k1_xboole_0 != sK4
    | v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK4) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f508,plain,
    ( spl7_50
    | spl7_65
    | ~ spl7_51 ),
    inference(avatar_split_clause,[],[f503,f412,f505,f407])).

fof(f412,plain,
    ( spl7_51
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | k1_xboole_0 = k7_relat_1(sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f503,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK6(sK2))
    | k1_xboole_0 = sK2
    | ~ spl7_51 ),
    inference(resolution,[],[f413,f76])).

fof(f76,plain,(
    ! [X0] :
      ( r1_xboole_0(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r1_xboole_0(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r1_xboole_0(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f413,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f412])).

fof(f486,plain,
    ( ~ spl7_24
    | spl7_64
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f466,f387,f484,f221])).

fof(f387,plain,
    ( spl7_47
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f466,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK3)
        | ~ v1_relat_1(sK5)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl7_47 ),
    inference(superposition,[],[f74,f389])).

fof(f389,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f387])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f458,plain,
    ( spl7_1
    | spl7_4
    | spl7_59
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f451,f114,f456,f119,f104])).

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
    inference(resolution,[],[f94,f116])).

fof(f116,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f94,plain,(
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
    inference(cnf_transformation,[],[f51])).

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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f442,plain,
    ( spl7_1
    | spl7_4
    | spl7_56
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f435,f114,f440,f119,f104])).

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
    inference(resolution,[],[f93,f116])).

fof(f93,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f422,plain,
    ( spl7_1
    | spl7_4
    | spl7_52
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f415,f114,f420,f119,f104])).

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
    inference(resolution,[],[f92,f116])).

fof(f92,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f414,plain,
    ( ~ spl7_23
    | spl7_51
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f394,f371,f412,f216])).

fof(f394,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | ~ v1_relat_1(sK4)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl7_44 ),
    inference(superposition,[],[f74,f373])).

fof(f390,plain,
    ( ~ spl7_24
    | spl7_47
    | ~ spl7_34
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f385,f365,f286,f387,f221])).

fof(f286,plain,
    ( spl7_34
  <=> v4_relat_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f365,plain,
    ( spl7_43
  <=> v1_partfun1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f385,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl7_43 ),
    inference(resolution,[],[f367,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f367,plain,
    ( v1_partfun1(sK5,sK3)
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f365])).

fof(f384,plain,
    ( spl7_46
    | ~ spl7_13
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f376,f154,f164,f382])).

fof(f376,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK5)
        | k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) )
    | ~ spl7_11 ),
    inference(resolution,[],[f91,f156])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f380,plain,
    ( spl7_45
    | ~ spl7_10
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f375,f139,f149,f378])).

fof(f375,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) )
    | ~ spl7_8 ),
    inference(resolution,[],[f91,f141])).

fof(f374,plain,
    ( ~ spl7_23
    | spl7_44
    | ~ spl7_33
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f369,f360,f281,f371,f216])).

fof(f281,plain,
    ( spl7_33
  <=> v4_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f360,plain,
    ( spl7_42
  <=> v1_partfun1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f369,plain,
    ( ~ v4_relat_1(sK4,sK2)
    | sK2 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl7_42 ),
    inference(resolution,[],[f362,f84])).

fof(f362,plain,
    ( v1_partfun1(sK4,sK2)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f360])).

fof(f368,plain,
    ( spl7_43
    | ~ spl7_12
    | ~ spl7_13
    | spl7_2
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f358,f154,f109,f164,f159,f365])).

fof(f358,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | ~ spl7_11 ),
    inference(resolution,[],[f78,f156])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f363,plain,
    ( spl7_42
    | ~ spl7_9
    | ~ spl7_10
    | spl7_2
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f357,f139,f109,f149,f144,f360])).

fof(f357,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f78,f141])).

fof(f309,plain,
    ( spl7_36
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f304,f299,f306])).

fof(f304,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl7_35 ),
    inference(resolution,[],[f301,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f86,f77])).

fof(f86,plain,(
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
    inference(avatar_split_clause,[],[f297,f124,f134,f299,f119])).

fof(f124,plain,
    ( spl7_5
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f297,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2)
    | ~ spl7_5 ),
    inference(resolution,[],[f82,f126])).

fof(f126,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f289,plain,
    ( spl7_34
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f279,f154,f286])).

fof(f279,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl7_11 ),
    inference(resolution,[],[f90,f156])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f284,plain,
    ( spl7_33
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f278,f139,f281])).

fof(f278,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f90,f141])).

fof(f242,plain,
    ( spl7_27
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f227,f216,f239])).

fof(f239,plain,
    ( spl7_27
  <=> sK4 = k7_relat_1(sK4,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f227,plain,
    ( sK4 = k7_relat_1(sK4,k1_relat_1(sK4))
    | ~ spl7_23 ),
    inference(resolution,[],[f218,f71])).

fof(f237,plain,
    ( spl7_25
    | ~ spl7_26
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f225,f216,f234,f230])).

fof(f230,plain,
    ( spl7_25
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f225,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | k1_xboole_0 = sK4
    | ~ spl7_23 ),
    inference(resolution,[],[f218,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f224,plain,
    ( spl7_24
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f214,f154,f221])).

fof(f214,plain,
    ( v1_relat_1(sK5)
    | ~ spl7_11 ),
    inference(resolution,[],[f89,f156])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f219,plain,
    ( spl7_23
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f213,f139,f216])).

fof(f213,plain,
    ( v1_relat_1(sK4)
    | ~ spl7_8 ),
    inference(resolution,[],[f89,f141])).

fof(f190,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f66,f187])).

fof(f66,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f180,plain,
    ( ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f52,f177,f173,f169])).

fof(f52,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f26])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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

fof(f167,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f53,f164])).

fof(f53,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f162,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f54,f159])).

fof(f54,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f157,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f55,f154])).

fof(f55,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f152,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f56,f149])).

fof(f56,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f147,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f57,f144])).

fof(f57,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f142,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f58,f139])).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f137,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f59,f134])).

fof(f59,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f132,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f60,f129])).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f127,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f61,f124])).

fof(f61,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f122,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f62,f119])).

fof(f62,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f117,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f63,f114])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f112,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f64,f109])).

fof(f64,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f107,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f65,f104])).

fof(f65,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (8245)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (8229)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (8226)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (8237)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (8241)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (8230)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (8228)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (8242)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (8246)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (8234)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (8223)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (8225)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (8244)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (8227)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (8250)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (8224)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (8252)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (8222)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (8249)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (8240)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (8251)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (8232)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (8236)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (8231)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (8233)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (8239)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (8247)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (8243)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (8238)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (8239)Refutation not found, incomplete strategy% (8239)------------------------------
% 0.21/0.55  % (8239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8235)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.57  % (8244)Refutation not found, incomplete strategy% (8244)------------------------------
% 0.21/0.57  % (8244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (8239)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (8239)Memory used [KB]: 10746
% 0.21/0.57  % (8239)Time elapsed: 0.146 s
% 0.21/0.57  % (8239)------------------------------
% 0.21/0.57  % (8239)------------------------------
% 0.21/0.58  % (8244)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (8244)Memory used [KB]: 11513
% 0.21/0.58  % (8244)Time elapsed: 0.144 s
% 0.21/0.58  % (8244)------------------------------
% 0.21/0.58  % (8244)------------------------------
% 1.83/0.61  % (8232)Refutation not found, incomplete strategy% (8232)------------------------------
% 1.83/0.61  % (8232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.62  % (8238)Refutation found. Thanks to Tanya!
% 1.99/0.62  % SZS status Theorem for theBenchmark
% 1.99/0.62  % (8232)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.62  
% 1.99/0.62  % (8232)Memory used [KB]: 11513
% 1.99/0.62  % (8232)Time elapsed: 0.191 s
% 1.99/0.62  % (8232)------------------------------
% 1.99/0.62  % (8232)------------------------------
% 2.09/0.64  % SZS output start Proof for theBenchmark
% 2.09/0.64  fof(f1675,plain,(
% 2.09/0.64    $false),
% 2.09/0.64    inference(avatar_sat_refutation,[],[f107,f112,f117,f122,f127,f132,f137,f142,f147,f152,f157,f162,f167,f180,f190,f219,f224,f237,f242,f284,f289,f302,f309,f363,f368,f374,f380,f384,f390,f414,f422,f442,f458,f486,f508,f509,f537,f539,f540,f552,f622,f639,f667,f677,f698,f754,f808,f878,f907,f967,f1578,f1586,f1672,f1674])).
% 2.09/0.64  fof(f1674,plain,(
% 2.09/0.64    k1_xboole_0 != k1_relat_1(k1_xboole_0) | sK4 != k7_relat_1(sK4,k1_relat_1(sK4)) | k1_xboole_0 != sK4 | k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 2.09/0.64    introduced(theory_tautology_sat_conflict,[])).
% 2.09/0.64  fof(f1672,plain,(
% 2.09/0.64    ~spl7_92 | ~spl7_6 | spl7_16 | ~spl7_36 | ~spl7_45 | ~spl7_46 | ~spl7_97),
% 2.09/0.64    inference(avatar_split_clause,[],[f1671,f797,f382,f378,f306,f177,f129,f751])).
% 2.09/0.64  fof(f751,plain,(
% 2.09/0.64    spl7_92 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).
% 2.09/0.64  fof(f129,plain,(
% 2.09/0.64    spl7_6 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 2.09/0.64  fof(f177,plain,(
% 2.09/0.64    spl7_16 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 2.09/0.64  fof(f306,plain,(
% 2.09/0.64    spl7_36 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 2.09/0.64  fof(f378,plain,(
% 2.09/0.64    spl7_45 <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 2.09/0.64  fof(f382,plain,(
% 2.09/0.64    spl7_46 <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 2.09/0.64  fof(f797,plain,(
% 2.09/0.64    spl7_97 <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).
% 2.09/0.64  fof(f1671,plain,(
% 2.09/0.64    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | (~spl7_6 | spl7_16 | ~spl7_36 | ~spl7_45 | ~spl7_46 | ~spl7_97)),
% 2.09/0.64    inference(forward_demodulation,[],[f1670,f799])).
% 2.09/0.64  fof(f799,plain,(
% 2.09/0.64    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | ~spl7_97),
% 2.09/0.64    inference(avatar_component_clause,[],[f797])).
% 2.09/0.64  fof(f1670,plain,(
% 2.09/0.64    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | (~spl7_6 | spl7_16 | ~spl7_36 | ~spl7_45 | ~spl7_46)),
% 2.09/0.64    inference(forward_demodulation,[],[f1669,f379])).
% 2.09/0.64  fof(f379,plain,(
% 2.09/0.64    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl7_45),
% 2.09/0.64    inference(avatar_component_clause,[],[f378])).
% 2.09/0.64  fof(f1669,plain,(
% 2.09/0.64    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (~spl7_6 | spl7_16 | ~spl7_36 | ~spl7_46)),
% 2.09/0.64    inference(forward_demodulation,[],[f1668,f308])).
% 2.09/0.64  fof(f308,plain,(
% 2.09/0.64    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl7_36),
% 2.09/0.64    inference(avatar_component_clause,[],[f306])).
% 2.09/0.64  fof(f1668,plain,(
% 2.09/0.64    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | (~spl7_6 | spl7_16 | ~spl7_46)),
% 2.09/0.64    inference(forward_demodulation,[],[f1667,f334])).
% 2.09/0.64  fof(f334,plain,(
% 2.09/0.64    ( ! [X1] : (k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))) ) | ~spl7_6),
% 2.09/0.64    inference(resolution,[],[f97,f131])).
% 2.09/0.64  fof(f131,plain,(
% 2.09/0.64    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl7_6),
% 2.09/0.64    inference(avatar_component_clause,[],[f129])).
% 2.09/0.64  fof(f97,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 2.09/0.64    inference(definition_unfolding,[],[f88,f77])).
% 2.09/0.64  fof(f77,plain,(
% 2.09/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f4])).
% 2.09/0.64  fof(f4,axiom,(
% 2.09/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.09/0.64  fof(f88,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f45])).
% 2.09/0.64  fof(f45,plain,(
% 2.09/0.64    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.09/0.64    inference(ennf_transformation,[],[f2])).
% 2.09/0.64  fof(f2,axiom,(
% 2.09/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.09/0.64  fof(f1667,plain,(
% 2.09/0.64    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (spl7_16 | ~spl7_46)),
% 2.09/0.64    inference(forward_demodulation,[],[f179,f383])).
% 2.09/0.64  fof(f383,plain,(
% 2.09/0.64    ( ! [X1] : (k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl7_46),
% 2.09/0.64    inference(avatar_component_clause,[],[f382])).
% 2.09/0.64  fof(f179,plain,(
% 2.09/0.64    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl7_16),
% 2.09/0.64    inference(avatar_component_clause,[],[f177])).
% 2.09/0.64  fof(f1586,plain,(
% 2.09/0.64    spl7_14 | spl7_1 | ~spl7_108 | ~spl7_104 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_6 | spl7_7 | ~spl7_3 | spl7_4 | spl7_2 | ~spl7_6 | ~spl7_36 | ~spl7_45 | ~spl7_46 | ~spl7_92 | ~spl7_97 | ~spl7_113),
% 2.09/0.64    inference(avatar_split_clause,[],[f1585,f964,f797,f751,f382,f378,f306,f129,f109,f119,f114,f134,f129,f149,f144,f139,f164,f159,f154,f875,f904,f104,f169])).
% 2.09/0.64  fof(f169,plain,(
% 2.09/0.64    spl7_14 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 2.09/0.64  fof(f104,plain,(
% 2.09/0.64    spl7_1 <=> v1_xboole_0(sK0)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.09/0.64  fof(f904,plain,(
% 2.09/0.64    spl7_108 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).
% 2.09/0.64  fof(f875,plain,(
% 2.09/0.64    spl7_104 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).
% 2.09/0.64  fof(f154,plain,(
% 2.09/0.64    spl7_11 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 2.09/0.64  fof(f159,plain,(
% 2.09/0.64    spl7_12 <=> v1_funct_2(sK5,sK3,sK1)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 2.09/0.64  fof(f164,plain,(
% 2.09/0.64    spl7_13 <=> v1_funct_1(sK5)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 2.09/0.64  fof(f139,plain,(
% 2.09/0.64    spl7_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 2.09/0.64  fof(f144,plain,(
% 2.09/0.64    spl7_9 <=> v1_funct_2(sK4,sK2,sK1)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 2.09/0.64  fof(f149,plain,(
% 2.09/0.64    spl7_10 <=> v1_funct_1(sK4)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 2.09/0.64  fof(f134,plain,(
% 2.09/0.64    spl7_7 <=> v1_xboole_0(sK3)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 2.09/0.64  fof(f114,plain,(
% 2.09/0.64    spl7_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.09/0.64  fof(f119,plain,(
% 2.09/0.64    spl7_4 <=> v1_xboole_0(sK2)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.09/0.64  fof(f109,plain,(
% 2.09/0.64    spl7_2 <=> v1_xboole_0(sK1)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.09/0.64  fof(f964,plain,(
% 2.09/0.64    spl7_113 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).
% 2.09/0.64  fof(f1585,plain,(
% 2.09/0.64    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_36 | ~spl7_45 | ~spl7_46 | ~spl7_92 | ~spl7_97 | ~spl7_113)),
% 2.09/0.64    inference(trivial_inequality_removal,[],[f1584])).
% 2.09/0.64  fof(f1584,plain,(
% 2.09/0.64    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_36 | ~spl7_45 | ~spl7_46 | ~spl7_92 | ~spl7_97 | ~spl7_113)),
% 2.09/0.64    inference(forward_demodulation,[],[f1583,f753])).
% 2.09/0.64  fof(f753,plain,(
% 2.09/0.64    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl7_92),
% 2.09/0.64    inference(avatar_component_clause,[],[f751])).
% 2.09/0.64  fof(f1583,plain,(
% 2.09/0.64    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_36 | ~spl7_45 | ~spl7_46 | ~spl7_97 | ~spl7_113)),
% 2.09/0.64    inference(forward_demodulation,[],[f1582,f799])).
% 2.09/0.64  fof(f1582,plain,(
% 2.09/0.64    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_36 | ~spl7_45 | ~spl7_46 | ~spl7_113)),
% 2.09/0.64    inference(forward_demodulation,[],[f1581,f379])).
% 2.09/0.64  fof(f1581,plain,(
% 2.09/0.64    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_36 | ~spl7_46 | ~spl7_113)),
% 2.09/0.64    inference(forward_demodulation,[],[f1580,f308])).
% 2.09/0.64  fof(f1580,plain,(
% 2.09/0.64    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_6 | ~spl7_46 | ~spl7_113)),
% 2.09/0.64    inference(forward_demodulation,[],[f1579,f334])).
% 2.09/0.64  fof(f1579,plain,(
% 2.09/0.64    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl7_46 | ~spl7_113)),
% 2.09/0.64    inference(forward_demodulation,[],[f1554,f383])).
% 2.09/0.64  fof(f1554,plain,(
% 2.09/0.64    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~spl7_113),
% 2.09/0.64    inference(resolution,[],[f966,f100])).
% 2.09/0.64  fof(f100,plain,(
% 2.09/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 2.09/0.64    inference(equality_resolution,[],[f69])).
% 2.09/0.64  fof(f69,plain,(
% 2.09/0.64    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 2.09/0.64    inference(cnf_transformation,[],[f28])).
% 2.09/0.64  fof(f28,plain,(
% 2.09/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.09/0.64    inference(flattening,[],[f27])).
% 2.09/0.64  fof(f27,plain,(
% 2.09/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.09/0.64    inference(ennf_transformation,[],[f19])).
% 2.09/0.64  fof(f19,axiom,(
% 2.09/0.64    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 2.09/0.64  fof(f966,plain,(
% 2.09/0.64    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl7_113),
% 2.09/0.64    inference(avatar_component_clause,[],[f964])).
% 2.09/0.64  fof(f1578,plain,(
% 2.09/0.64    spl7_15 | spl7_1 | ~spl7_108 | ~spl7_104 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_6 | spl7_7 | ~spl7_3 | spl7_4 | spl7_2 | ~spl7_6 | ~spl7_36 | ~spl7_45 | ~spl7_46 | ~spl7_92 | ~spl7_97 | ~spl7_113),
% 2.09/0.64    inference(avatar_split_clause,[],[f1577,f964,f797,f751,f382,f378,f306,f129,f109,f119,f114,f134,f129,f149,f144,f139,f164,f159,f154,f875,f904,f104,f173])).
% 2.09/0.64  fof(f173,plain,(
% 2.09/0.64    spl7_15 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 2.09/0.64  fof(f1577,plain,(
% 2.09/0.64    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_36 | ~spl7_45 | ~spl7_46 | ~spl7_92 | ~spl7_97 | ~spl7_113)),
% 2.09/0.64    inference(trivial_inequality_removal,[],[f1576])).
% 2.09/0.64  fof(f1576,plain,(
% 2.09/0.64    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_36 | ~spl7_45 | ~spl7_46 | ~spl7_92 | ~spl7_97 | ~spl7_113)),
% 2.09/0.64    inference(forward_demodulation,[],[f1575,f753])).
% 2.09/0.64  fof(f1575,plain,(
% 2.09/0.64    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_36 | ~spl7_45 | ~spl7_46 | ~spl7_97 | ~spl7_113)),
% 2.09/0.64    inference(forward_demodulation,[],[f1574,f799])).
% 2.09/0.64  fof(f1574,plain,(
% 2.09/0.64    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_36 | ~spl7_45 | ~spl7_46 | ~spl7_113)),
% 2.09/0.64    inference(forward_demodulation,[],[f1573,f379])).
% 2.09/0.64  fof(f1573,plain,(
% 2.09/0.64    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_36 | ~spl7_46 | ~spl7_113)),
% 2.09/0.64    inference(forward_demodulation,[],[f1572,f308])).
% 2.09/0.64  fof(f1572,plain,(
% 2.09/0.64    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_6 | ~spl7_46 | ~spl7_113)),
% 2.09/0.64    inference(forward_demodulation,[],[f1571,f334])).
% 2.09/0.64  fof(f1571,plain,(
% 2.09/0.64    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl7_46 | ~spl7_113)),
% 2.09/0.64    inference(forward_demodulation,[],[f1553,f383])).
% 2.09/0.64  fof(f1553,plain,(
% 2.09/0.64    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~spl7_113),
% 2.09/0.64    inference(resolution,[],[f966,f101])).
% 2.09/0.64  fof(f101,plain,(
% 2.09/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 2.09/0.64    inference(equality_resolution,[],[f68])).
% 2.09/0.64  fof(f68,plain,(
% 2.09/0.64    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 2.09/0.64    inference(cnf_transformation,[],[f28])).
% 2.09/0.64  fof(f967,plain,(
% 2.09/0.64    spl7_113 | ~spl7_10 | ~spl7_9 | ~spl7_8 | ~spl7_89),
% 2.09/0.64    inference(avatar_split_clause,[],[f962,f696,f139,f144,f149,f964])).
% 2.09/0.64  fof(f696,plain,(
% 2.09/0.64    spl7_89 <=> ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).
% 2.09/0.64  fof(f962,plain,(
% 2.09/0.64    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl7_8 | ~spl7_89)),
% 2.09/0.64    inference(resolution,[],[f697,f141])).
% 2.09/0.64  fof(f141,plain,(
% 2.09/0.64    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl7_8),
% 2.09/0.64    inference(avatar_component_clause,[],[f139])).
% 2.09/0.64  fof(f697,plain,(
% 2.09/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))) ) | ~spl7_89),
% 2.09/0.64    inference(avatar_component_clause,[],[f696])).
% 2.09/0.64  fof(f907,plain,(
% 2.09/0.64    spl7_108 | ~spl7_10 | ~spl7_9 | ~spl7_8 | ~spl7_85),
% 2.09/0.64    inference(avatar_split_clause,[],[f902,f675,f139,f144,f149,f904])).
% 2.09/0.64  fof(f675,plain,(
% 2.09/0.64    spl7_85 <=> ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).
% 2.09/0.64  fof(f902,plain,(
% 2.09/0.64    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl7_8 | ~spl7_85)),
% 2.09/0.64    inference(resolution,[],[f676,f141])).
% 2.09/0.64  fof(f676,plain,(
% 2.09/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)) ) | ~spl7_85),
% 2.09/0.64    inference(avatar_component_clause,[],[f675])).
% 2.09/0.64  fof(f878,plain,(
% 2.09/0.64    spl7_104 | ~spl7_10 | ~spl7_9 | ~spl7_8 | ~spl7_75),
% 2.09/0.64    inference(avatar_split_clause,[],[f873,f620,f139,f144,f149,f875])).
% 2.09/0.64  fof(f620,plain,(
% 2.09/0.64    spl7_75 <=> ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).
% 2.09/0.64  fof(f873,plain,(
% 2.09/0.64    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl7_8 | ~spl7_75)),
% 2.09/0.64    inference(resolution,[],[f621,f141])).
% 2.09/0.64  fof(f621,plain,(
% 2.09/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))) ) | ~spl7_75),
% 2.09/0.64    inference(avatar_component_clause,[],[f620])).
% 2.09/0.64  fof(f808,plain,(
% 2.09/0.64    spl7_97 | ~spl7_24 | ~spl7_70 | ~spl7_78 | ~spl7_83),
% 2.09/0.64    inference(avatar_split_clause,[],[f807,f664,f636,f549,f221,f797])).
% 2.09/0.64  fof(f221,plain,(
% 2.09/0.64    spl7_24 <=> v1_relat_1(sK5)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 2.09/0.64  fof(f549,plain,(
% 2.09/0.64    spl7_70 <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).
% 2.09/0.64  fof(f636,plain,(
% 2.09/0.64    spl7_78 <=> k1_xboole_0 = k7_relat_1(sK5,sK2)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).
% 2.09/0.64  fof(f664,plain,(
% 2.09/0.64    spl7_83 <=> r1_tarski(k1_xboole_0,sK2)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).
% 2.09/0.64  fof(f807,plain,(
% 2.09/0.64    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | (~spl7_24 | ~spl7_70 | ~spl7_78 | ~spl7_83)),
% 2.09/0.64    inference(forward_demodulation,[],[f806,f551])).
% 2.09/0.64  fof(f551,plain,(
% 2.09/0.64    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | ~spl7_70),
% 2.09/0.64    inference(avatar_component_clause,[],[f549])).
% 2.09/0.64  fof(f806,plain,(
% 2.09/0.64    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(sK5,k1_xboole_0) | (~spl7_24 | ~spl7_78 | ~spl7_83)),
% 2.09/0.64    inference(forward_demodulation,[],[f780,f638])).
% 2.09/0.64  fof(f638,plain,(
% 2.09/0.64    k1_xboole_0 = k7_relat_1(sK5,sK2) | ~spl7_78),
% 2.09/0.64    inference(avatar_component_clause,[],[f636])).
% 2.09/0.64  fof(f780,plain,(
% 2.09/0.64    k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0) | (~spl7_24 | ~spl7_83)),
% 2.09/0.64    inference(resolution,[],[f345,f666])).
% 2.09/0.64  fof(f666,plain,(
% 2.09/0.64    r1_tarski(k1_xboole_0,sK2) | ~spl7_83),
% 2.09/0.64    inference(avatar_component_clause,[],[f664])).
% 2.09/0.64  fof(f345,plain,(
% 2.09/0.64    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k7_relat_1(sK5,X2) = k7_relat_1(k7_relat_1(sK5,X3),X2)) ) | ~spl7_24),
% 2.09/0.64    inference(resolution,[],[f87,f223])).
% 2.09/0.64  fof(f223,plain,(
% 2.09/0.64    v1_relat_1(sK5) | ~spl7_24),
% 2.09/0.64    inference(avatar_component_clause,[],[f221])).
% 2.09/0.64  fof(f87,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f44])).
% 2.09/0.64  fof(f44,plain,(
% 2.09/0.64    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 2.09/0.64    inference(flattening,[],[f43])).
% 2.09/0.64  fof(f43,plain,(
% 2.09/0.64    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 2.09/0.64    inference(ennf_transformation,[],[f6])).
% 2.09/0.64  fof(f6,axiom,(
% 2.09/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 2.09/0.64  fof(f754,plain,(
% 2.09/0.64    spl7_92 | ~spl7_23 | ~spl7_65 | ~spl7_67 | ~spl7_70),
% 2.09/0.64    inference(avatar_split_clause,[],[f749,f549,f522,f505,f216,f751])).
% 2.09/0.64  fof(f216,plain,(
% 2.09/0.64    spl7_23 <=> v1_relat_1(sK4)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 2.09/0.64  fof(f505,plain,(
% 2.09/0.64    spl7_65 <=> k1_xboole_0 = k7_relat_1(sK4,sK6(sK2))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).
% 2.09/0.64  fof(f522,plain,(
% 2.09/0.64    spl7_67 <=> r1_tarski(k1_xboole_0,sK6(sK2))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).
% 2.09/0.64  fof(f749,plain,(
% 2.09/0.64    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | (~spl7_23 | ~spl7_65 | ~spl7_67 | ~spl7_70)),
% 2.09/0.64    inference(forward_demodulation,[],[f748,f551])).
% 2.09/0.64  fof(f748,plain,(
% 2.09/0.64    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0) | (~spl7_23 | ~spl7_65 | ~spl7_67)),
% 2.09/0.64    inference(forward_demodulation,[],[f736,f507])).
% 2.09/0.64  fof(f507,plain,(
% 2.09/0.64    k1_xboole_0 = k7_relat_1(sK4,sK6(sK2)) | ~spl7_65),
% 2.09/0.64    inference(avatar_component_clause,[],[f505])).
% 2.09/0.64  fof(f736,plain,(
% 2.09/0.64    k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k7_relat_1(sK4,sK6(sK2)),k1_xboole_0) | (~spl7_23 | ~spl7_67)),
% 2.09/0.64    inference(resolution,[],[f344,f524])).
% 2.09/0.64  fof(f524,plain,(
% 2.09/0.64    r1_tarski(k1_xboole_0,sK6(sK2)) | ~spl7_67),
% 2.09/0.64    inference(avatar_component_clause,[],[f522])).
% 2.09/0.64  fof(f344,plain,(
% 2.09/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(sK4,X0) = k7_relat_1(k7_relat_1(sK4,X1),X0)) ) | ~spl7_23),
% 2.09/0.64    inference(resolution,[],[f87,f218])).
% 2.09/0.64  fof(f218,plain,(
% 2.09/0.64    v1_relat_1(sK4) | ~spl7_23),
% 2.09/0.64    inference(avatar_component_clause,[],[f216])).
% 2.09/0.64  fof(f698,plain,(
% 2.09/0.64    ~spl7_6 | ~spl7_12 | spl7_7 | ~spl7_13 | spl7_2 | spl7_89 | ~spl7_11 | ~spl7_59),
% 2.09/0.64    inference(avatar_split_clause,[],[f690,f456,f154,f696,f109,f164,f134,f159,f129])).
% 2.09/0.64  fof(f456,plain,(
% 2.09/0.64    spl7_59 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).
% 2.09/0.64  fof(f690,plain,(
% 2.09/0.64    ( ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl7_11 | ~spl7_59)),
% 2.09/0.64    inference(resolution,[],[f457,f156])).
% 2.09/0.64  fof(f156,plain,(
% 2.09/0.64    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl7_11),
% 2.09/0.64    inference(avatar_component_clause,[],[f154])).
% 2.09/0.64  fof(f457,plain,(
% 2.09/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl7_59),
% 2.09/0.64    inference(avatar_component_clause,[],[f456])).
% 2.09/0.64  fof(f677,plain,(
% 2.09/0.64    ~spl7_6 | ~spl7_12 | spl7_7 | ~spl7_13 | spl7_2 | spl7_85 | ~spl7_11 | ~spl7_56),
% 2.09/0.64    inference(avatar_split_clause,[],[f669,f440,f154,f675,f109,f164,f134,f159,f129])).
% 2.09/0.64  fof(f440,plain,(
% 2.09/0.64    spl7_56 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 2.09/0.64  fof(f669,plain,(
% 2.09/0.64    ( ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl7_11 | ~spl7_56)),
% 2.09/0.64    inference(resolution,[],[f441,f156])).
% 2.09/0.64  fof(f441,plain,(
% 2.09/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl7_56),
% 2.09/0.64    inference(avatar_component_clause,[],[f440])).
% 2.09/0.64  fof(f667,plain,(
% 2.09/0.64    spl7_83 | ~spl7_18 | ~spl7_24 | ~spl7_78),
% 2.09/0.64    inference(avatar_split_clause,[],[f662,f636,f221,f187,f664])).
% 2.09/0.64  fof(f187,plain,(
% 2.09/0.64    spl7_18 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 2.09/0.64  fof(f662,plain,(
% 2.09/0.64    r1_tarski(k1_xboole_0,sK2) | (~spl7_18 | ~spl7_24 | ~spl7_78)),
% 2.09/0.64    inference(forward_demodulation,[],[f660,f189])).
% 2.09/0.64  fof(f189,plain,(
% 2.09/0.64    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_18),
% 2.09/0.64    inference(avatar_component_clause,[],[f187])).
% 2.09/0.64  fof(f660,plain,(
% 2.09/0.64    r1_tarski(k1_relat_1(k1_xboole_0),sK2) | (~spl7_24 | ~spl7_78)),
% 2.09/0.64    inference(superposition,[],[f244,f638])).
% 2.09/0.64  fof(f244,plain,(
% 2.09/0.64    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),X0)) ) | ~spl7_24),
% 2.09/0.64    inference(resolution,[],[f223,f80])).
% 2.09/0.64  fof(f80,plain,(
% 2.09/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f38])).
% 2.09/0.64  fof(f38,plain,(
% 2.09/0.64    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.09/0.64    inference(ennf_transformation,[],[f10])).
% 2.09/0.64  fof(f10,axiom,(
% 2.09/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 2.09/0.64  fof(f639,plain,(
% 2.09/0.64    spl7_78 | ~spl7_35 | ~spl7_64),
% 2.09/0.64    inference(avatar_split_clause,[],[f634,f484,f299,f636])).
% 2.09/0.64  fof(f299,plain,(
% 2.09/0.64    spl7_35 <=> r1_xboole_0(sK2,sK3)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 2.09/0.64  fof(f484,plain,(
% 2.09/0.64    spl7_64 <=> ! [X0] : (~r1_xboole_0(X0,sK3) | k1_xboole_0 = k7_relat_1(sK5,X0))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).
% 2.09/0.64  fof(f634,plain,(
% 2.09/0.64    k1_xboole_0 = k7_relat_1(sK5,sK2) | (~spl7_35 | ~spl7_64)),
% 2.09/0.64    inference(resolution,[],[f485,f301])).
% 2.09/0.64  fof(f301,plain,(
% 2.09/0.64    r1_xboole_0(sK2,sK3) | ~spl7_35),
% 2.09/0.64    inference(avatar_component_clause,[],[f299])).
% 2.09/0.64  fof(f485,plain,(
% 2.09/0.64    ( ! [X0] : (~r1_xboole_0(X0,sK3) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl7_64),
% 2.09/0.64    inference(avatar_component_clause,[],[f484])).
% 2.09/0.64  fof(f622,plain,(
% 2.09/0.64    ~spl7_6 | ~spl7_12 | spl7_7 | ~spl7_13 | spl7_2 | spl7_75 | ~spl7_11 | ~spl7_52),
% 2.09/0.64    inference(avatar_split_clause,[],[f614,f420,f154,f620,f109,f164,f134,f159,f129])).
% 2.09/0.64  fof(f420,plain,(
% 2.09/0.64    spl7_52 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 2.09/0.64  fof(f614,plain,(
% 2.09/0.64    ( ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl7_11 | ~spl7_52)),
% 2.09/0.64    inference(resolution,[],[f421,f156])).
% 2.09/0.64  fof(f421,plain,(
% 2.09/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl7_52),
% 2.09/0.64    inference(avatar_component_clause,[],[f420])).
% 2.09/0.64  fof(f552,plain,(
% 2.09/0.64    spl7_70 | ~spl7_18 | ~spl7_38),
% 2.09/0.64    inference(avatar_split_clause,[],[f547,f316,f187,f549])).
% 2.09/0.64  fof(f316,plain,(
% 2.09/0.64    spl7_38 <=> v1_relat_1(k1_xboole_0)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 2.09/0.64  fof(f547,plain,(
% 2.09/0.64    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | (~spl7_18 | ~spl7_38)),
% 2.09/0.64    inference(forward_demodulation,[],[f545,f189])).
% 2.09/0.64  fof(f545,plain,(
% 2.09/0.64    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) | ~spl7_38),
% 2.09/0.64    inference(resolution,[],[f317,f71])).
% 2.09/0.64  fof(f71,plain,(
% 2.09/0.64    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 2.09/0.64    inference(cnf_transformation,[],[f29])).
% 2.09/0.64  fof(f29,plain,(
% 2.09/0.64    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.09/0.64    inference(ennf_transformation,[],[f11])).
% 2.09/0.64  fof(f11,axiom,(
% 2.09/0.64    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 2.09/0.64  fof(f317,plain,(
% 2.09/0.64    v1_relat_1(k1_xboole_0) | ~spl7_38),
% 2.09/0.64    inference(avatar_component_clause,[],[f316])).
% 2.09/0.64  fof(f540,plain,(
% 2.09/0.64    ~spl7_50 | spl7_26 | ~spl7_44),
% 2.09/0.64    inference(avatar_split_clause,[],[f393,f371,f234,f407])).
% 2.09/0.64  fof(f407,plain,(
% 2.09/0.64    spl7_50 <=> k1_xboole_0 = sK2),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 2.09/0.64  fof(f234,plain,(
% 2.09/0.64    spl7_26 <=> k1_xboole_0 = k1_relat_1(sK4)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 2.09/0.64  fof(f371,plain,(
% 2.09/0.64    spl7_44 <=> sK2 = k1_relat_1(sK4)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 2.09/0.64  fof(f393,plain,(
% 2.09/0.64    k1_xboole_0 != sK2 | (spl7_26 | ~spl7_44)),
% 2.09/0.64    inference(superposition,[],[f236,f373])).
% 2.09/0.64  fof(f373,plain,(
% 2.09/0.64    sK2 = k1_relat_1(sK4) | ~spl7_44),
% 2.09/0.64    inference(avatar_component_clause,[],[f371])).
% 2.09/0.64  fof(f236,plain,(
% 2.09/0.64    k1_xboole_0 != k1_relat_1(sK4) | spl7_26),
% 2.09/0.64    inference(avatar_component_clause,[],[f234])).
% 2.09/0.64  fof(f539,plain,(
% 2.09/0.64    spl7_67 | ~spl7_18 | ~spl7_23 | ~spl7_65),
% 2.09/0.64    inference(avatar_split_clause,[],[f538,f505,f216,f187,f522])).
% 2.09/0.64  fof(f538,plain,(
% 2.09/0.64    r1_tarski(k1_xboole_0,sK6(sK2)) | (~spl7_18 | ~spl7_23 | ~spl7_65)),
% 2.09/0.64    inference(forward_demodulation,[],[f518,f189])).
% 2.09/0.64  fof(f518,plain,(
% 2.09/0.64    r1_tarski(k1_relat_1(k1_xboole_0),sK6(sK2)) | (~spl7_23 | ~spl7_65)),
% 2.09/0.64    inference(superposition,[],[f226,f507])).
% 2.09/0.64  fof(f226,plain,(
% 2.09/0.64    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0)) ) | ~spl7_23),
% 2.09/0.64    inference(resolution,[],[f218,f80])).
% 2.09/0.64  fof(f537,plain,(
% 2.09/0.64    spl7_38 | ~spl7_23 | ~spl7_65),
% 2.09/0.64    inference(avatar_split_clause,[],[f519,f505,f216,f316])).
% 2.09/0.64  fof(f519,plain,(
% 2.09/0.64    v1_relat_1(k1_xboole_0) | (~spl7_23 | ~spl7_65)),
% 2.09/0.64    inference(superposition,[],[f228,f507])).
% 2.09/0.64  fof(f228,plain,(
% 2.09/0.64    ( ! [X1] : (v1_relat_1(k7_relat_1(sK4,X1))) ) | ~spl7_23),
% 2.09/0.64    inference(resolution,[],[f218,f79])).
% 2.09/0.64  fof(f79,plain,(
% 2.09/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f37])).
% 2.09/0.64  fof(f37,plain,(
% 2.09/0.64    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.09/0.64    inference(ennf_transformation,[],[f5])).
% 2.09/0.64  fof(f5,axiom,(
% 2.09/0.64    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.09/0.64  fof(f509,plain,(
% 2.09/0.64    k1_xboole_0 != sK4 | v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK4)),
% 2.09/0.64    introduced(theory_tautology_sat_conflict,[])).
% 2.09/0.65  fof(f508,plain,(
% 2.09/0.65    spl7_50 | spl7_65 | ~spl7_51),
% 2.09/0.65    inference(avatar_split_clause,[],[f503,f412,f505,f407])).
% 2.09/0.65  fof(f412,plain,(
% 2.09/0.65    spl7_51 <=> ! [X0] : (~r1_xboole_0(X0,sK2) | k1_xboole_0 = k7_relat_1(sK4,X0))),
% 2.09/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).
% 2.09/0.65  fof(f503,plain,(
% 2.09/0.65    k1_xboole_0 = k7_relat_1(sK4,sK6(sK2)) | k1_xboole_0 = sK2 | ~spl7_51),
% 2.09/0.65    inference(resolution,[],[f413,f76])).
% 2.09/0.65  fof(f76,plain,(
% 2.09/0.65    ( ! [X0] : (r1_xboole_0(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 2.09/0.65    inference(cnf_transformation,[],[f34])).
% 2.09/0.65  fof(f34,plain,(
% 2.09/0.65    ! [X0] : (? [X1] : r1_xboole_0(X1,X0) | k1_xboole_0 = X0)),
% 2.09/0.65    inference(ennf_transformation,[],[f23])).
% 2.09/0.65  fof(f23,plain,(
% 2.09/0.65    ! [X0] : ~(! [X1] : ~r1_xboole_0(X1,X0) & k1_xboole_0 != X0)),
% 2.09/0.65    inference(pure_predicate_removal,[],[f15])).
% 2.09/0.65  fof(f15,axiom,(
% 2.09/0.65    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.09/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 2.09/0.65  fof(f413,plain,(
% 2.09/0.65    ( ! [X0] : (~r1_xboole_0(X0,sK2) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl7_51),
% 2.09/0.65    inference(avatar_component_clause,[],[f412])).
% 2.09/0.65  fof(f486,plain,(
% 2.09/0.65    ~spl7_24 | spl7_64 | ~spl7_47),
% 2.09/0.65    inference(avatar_split_clause,[],[f466,f387,f484,f221])).
% 2.09/0.65  fof(f387,plain,(
% 2.09/0.65    spl7_47 <=> sK3 = k1_relat_1(sK5)),
% 2.09/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 2.09/0.65  fof(f466,plain,(
% 2.09/0.65    ( ! [X0] : (~r1_xboole_0(X0,sK3) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl7_47),
% 2.09/0.65    inference(superposition,[],[f74,f389])).
% 2.09/0.65  fof(f389,plain,(
% 2.09/0.65    sK3 = k1_relat_1(sK5) | ~spl7_47),
% 2.09/0.65    inference(avatar_component_clause,[],[f387])).
% 2.09/0.65  fof(f74,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f32])).
% 2.09/0.65  fof(f32,plain,(
% 2.09/0.65    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.09/0.65    inference(ennf_transformation,[],[f7])).
% 2.09/0.65  fof(f7,axiom,(
% 2.09/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 2.09/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 2.09/0.65  fof(f458,plain,(
% 2.09/0.65    spl7_1 | spl7_4 | spl7_59 | ~spl7_3),
% 2.09/0.65    inference(avatar_split_clause,[],[f451,f114,f456,f119,f104])).
% 2.09/0.65  fof(f451,plain,(
% 2.09/0.65    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0)))) ) | ~spl7_3),
% 2.09/0.65    inference(resolution,[],[f94,f116])).
% 2.09/0.65  fof(f116,plain,(
% 2.09/0.65    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl7_3),
% 2.09/0.65    inference(avatar_component_clause,[],[f114])).
% 2.09/0.65  fof(f94,plain,(
% 2.09/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 2.09/0.65    inference(cnf_transformation,[],[f51])).
% 2.09/0.65  fof(f51,plain,(
% 2.09/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.09/0.65    inference(flattening,[],[f50])).
% 2.09/0.65  fof(f50,plain,(
% 2.09/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.09/0.65    inference(ennf_transformation,[],[f20])).
% 2.09/0.65  fof(f20,axiom,(
% 2.09/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 2.09/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 2.09/0.65  fof(f442,plain,(
% 2.09/0.65    spl7_1 | spl7_4 | spl7_56 | ~spl7_3),
% 2.09/0.65    inference(avatar_split_clause,[],[f435,f114,f440,f119,f104])).
% 2.09/0.65  fof(f435,plain,(
% 2.09/0.65    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0)) ) | ~spl7_3),
% 2.09/0.65    inference(resolution,[],[f93,f116])).
% 2.09/0.65  fof(f93,plain,(
% 2.09/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f51])).
% 2.09/0.65  fof(f422,plain,(
% 2.09/0.65    spl7_1 | spl7_4 | spl7_52 | ~spl7_3),
% 2.09/0.65    inference(avatar_split_clause,[],[f415,f114,f420,f119,f104])).
% 2.09/0.65  fof(f415,plain,(
% 2.09/0.65    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3))) ) | ~spl7_3),
% 2.09/0.65    inference(resolution,[],[f92,f116])).
% 2.09/0.65  fof(f92,plain,(
% 2.09/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 2.09/0.65    inference(cnf_transformation,[],[f51])).
% 2.09/0.65  fof(f414,plain,(
% 2.09/0.65    ~spl7_23 | spl7_51 | ~spl7_44),
% 2.09/0.65    inference(avatar_split_clause,[],[f394,f371,f412,f216])).
% 2.09/0.65  fof(f394,plain,(
% 2.09/0.65    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~v1_relat_1(sK4) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl7_44),
% 2.09/0.65    inference(superposition,[],[f74,f373])).
% 2.09/0.65  fof(f390,plain,(
% 2.09/0.65    ~spl7_24 | spl7_47 | ~spl7_34 | ~spl7_43),
% 2.09/0.65    inference(avatar_split_clause,[],[f385,f365,f286,f387,f221])).
% 2.09/0.65  fof(f286,plain,(
% 2.09/0.65    spl7_34 <=> v4_relat_1(sK5,sK3)),
% 2.09/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 2.09/0.65  fof(f365,plain,(
% 2.09/0.65    spl7_43 <=> v1_partfun1(sK5,sK3)),
% 2.09/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 2.09/0.65  fof(f385,plain,(
% 2.09/0.65    ~v4_relat_1(sK5,sK3) | sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5) | ~spl7_43),
% 2.09/0.65    inference(resolution,[],[f367,f84])).
% 2.09/0.65  fof(f84,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f42])).
% 2.09/0.65  fof(f42,plain,(
% 2.09/0.65    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.09/0.65    inference(flattening,[],[f41])).
% 2.09/0.65  fof(f41,plain,(
% 2.09/0.65    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.09/0.65    inference(ennf_transformation,[],[f17])).
% 2.09/0.65  fof(f17,axiom,(
% 2.09/0.65    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.09/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 2.09/0.65  fof(f367,plain,(
% 2.09/0.65    v1_partfun1(sK5,sK3) | ~spl7_43),
% 2.09/0.65    inference(avatar_component_clause,[],[f365])).
% 2.09/0.65  fof(f384,plain,(
% 2.09/0.65    spl7_46 | ~spl7_13 | ~spl7_11),
% 2.09/0.65    inference(avatar_split_clause,[],[f376,f154,f164,f382])).
% 2.09/0.65  fof(f376,plain,(
% 2.09/0.65    ( ! [X1] : (~v1_funct_1(sK5) | k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl7_11),
% 2.09/0.65    inference(resolution,[],[f91,f156])).
% 2.09/0.65  fof(f91,plain,(
% 2.09/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f49])).
% 2.09/0.65  fof(f49,plain,(
% 2.09/0.65    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.09/0.65    inference(flattening,[],[f48])).
% 2.09/0.65  fof(f48,plain,(
% 2.09/0.65    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.09/0.65    inference(ennf_transformation,[],[f18])).
% 2.09/0.65  fof(f18,axiom,(
% 2.09/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.09/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.09/0.65  fof(f380,plain,(
% 2.09/0.65    spl7_45 | ~spl7_10 | ~spl7_8),
% 2.09/0.65    inference(avatar_split_clause,[],[f375,f139,f149,f378])).
% 2.09/0.65  fof(f375,plain,(
% 2.09/0.65    ( ! [X0] : (~v1_funct_1(sK4) | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl7_8),
% 2.09/0.65    inference(resolution,[],[f91,f141])).
% 2.09/0.65  fof(f374,plain,(
% 2.09/0.65    ~spl7_23 | spl7_44 | ~spl7_33 | ~spl7_42),
% 2.09/0.65    inference(avatar_split_clause,[],[f369,f360,f281,f371,f216])).
% 2.09/0.65  fof(f281,plain,(
% 2.09/0.65    spl7_33 <=> v4_relat_1(sK4,sK2)),
% 2.09/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 2.09/0.65  fof(f360,plain,(
% 2.09/0.65    spl7_42 <=> v1_partfun1(sK4,sK2)),
% 2.09/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 2.09/0.65  fof(f369,plain,(
% 2.09/0.65    ~v4_relat_1(sK4,sK2) | sK2 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl7_42),
% 2.09/0.65    inference(resolution,[],[f362,f84])).
% 2.09/0.65  fof(f362,plain,(
% 2.09/0.65    v1_partfun1(sK4,sK2) | ~spl7_42),
% 2.09/0.65    inference(avatar_component_clause,[],[f360])).
% 2.09/0.65  fof(f368,plain,(
% 2.09/0.65    spl7_43 | ~spl7_12 | ~spl7_13 | spl7_2 | ~spl7_11),
% 2.09/0.65    inference(avatar_split_clause,[],[f358,f154,f109,f164,f159,f365])).
% 2.09/0.65  fof(f358,plain,(
% 2.09/0.65    v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3) | ~spl7_11),
% 2.09/0.65    inference(resolution,[],[f78,f156])).
% 2.09/0.65  fof(f78,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f36])).
% 2.09/0.65  fof(f36,plain,(
% 2.09/0.65    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.09/0.65    inference(flattening,[],[f35])).
% 2.09/0.65  fof(f35,plain,(
% 2.09/0.65    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.09/0.65    inference(ennf_transformation,[],[f16])).
% 2.09/0.65  fof(f16,axiom,(
% 2.09/0.65    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.09/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 2.09/0.65  fof(f363,plain,(
% 2.09/0.65    spl7_42 | ~spl7_9 | ~spl7_10 | spl7_2 | ~spl7_8),
% 2.09/0.65    inference(avatar_split_clause,[],[f357,f139,f109,f149,f144,f360])).
% 2.09/0.65  fof(f357,plain,(
% 2.09/0.65    v1_xboole_0(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2) | ~spl7_8),
% 2.09/0.65    inference(resolution,[],[f78,f141])).
% 2.09/0.65  fof(f309,plain,(
% 2.09/0.65    spl7_36 | ~spl7_35),
% 2.09/0.65    inference(avatar_split_clause,[],[f304,f299,f306])).
% 2.09/0.65  fof(f304,plain,(
% 2.09/0.65    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl7_35),
% 2.09/0.65    inference(resolution,[],[f301,f95])).
% 2.09/0.65  fof(f95,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.09/0.65    inference(definition_unfolding,[],[f86,f77])).
% 2.09/0.65  fof(f86,plain,(
% 2.09/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f1])).
% 2.09/0.65  fof(f1,axiom,(
% 2.09/0.65    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.09/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.09/0.65  fof(f302,plain,(
% 2.09/0.65    spl7_4 | spl7_35 | spl7_7 | ~spl7_5),
% 2.09/0.65    inference(avatar_split_clause,[],[f297,f124,f134,f299,f119])).
% 2.09/0.65  fof(f124,plain,(
% 2.09/0.65    spl7_5 <=> r1_subset_1(sK2,sK3)),
% 2.09/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.09/0.65  fof(f297,plain,(
% 2.09/0.65    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | ~spl7_5),
% 2.09/0.65    inference(resolution,[],[f82,f126])).
% 2.09/0.65  fof(f126,plain,(
% 2.09/0.65    r1_subset_1(sK2,sK3) | ~spl7_5),
% 2.09/0.65    inference(avatar_component_clause,[],[f124])).
% 2.09/0.65  fof(f82,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f40])).
% 2.09/0.65  fof(f40,plain,(
% 2.09/0.65    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.09/0.65    inference(flattening,[],[f39])).
% 2.09/0.65  fof(f39,plain,(
% 2.09/0.65    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.09/0.65    inference(ennf_transformation,[],[f12])).
% 2.09/0.65  fof(f12,axiom,(
% 2.09/0.65    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 2.09/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 2.09/0.65  fof(f289,plain,(
% 2.09/0.65    spl7_34 | ~spl7_11),
% 2.09/0.65    inference(avatar_split_clause,[],[f279,f154,f286])).
% 2.09/0.65  fof(f279,plain,(
% 2.09/0.65    v4_relat_1(sK5,sK3) | ~spl7_11),
% 2.09/0.65    inference(resolution,[],[f90,f156])).
% 2.09/0.65  fof(f90,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f47])).
% 2.09/0.65  fof(f47,plain,(
% 2.09/0.65    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.65    inference(ennf_transformation,[],[f24])).
% 2.09/0.65  fof(f24,plain,(
% 2.09/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.09/0.65    inference(pure_predicate_removal,[],[f14])).
% 2.09/0.65  fof(f14,axiom,(
% 2.09/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.09/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.09/0.65  fof(f284,plain,(
% 2.09/0.65    spl7_33 | ~spl7_8),
% 2.09/0.65    inference(avatar_split_clause,[],[f278,f139,f281])).
% 2.09/0.65  fof(f278,plain,(
% 2.09/0.65    v4_relat_1(sK4,sK2) | ~spl7_8),
% 2.09/0.65    inference(resolution,[],[f90,f141])).
% 2.09/0.65  fof(f242,plain,(
% 2.09/0.65    spl7_27 | ~spl7_23),
% 2.09/0.65    inference(avatar_split_clause,[],[f227,f216,f239])).
% 2.09/0.65  fof(f239,plain,(
% 2.09/0.65    spl7_27 <=> sK4 = k7_relat_1(sK4,k1_relat_1(sK4))),
% 2.09/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 2.09/0.65  fof(f227,plain,(
% 2.09/0.65    sK4 = k7_relat_1(sK4,k1_relat_1(sK4)) | ~spl7_23),
% 2.09/0.65    inference(resolution,[],[f218,f71])).
% 2.09/0.65  fof(f237,plain,(
% 2.09/0.65    spl7_25 | ~spl7_26 | ~spl7_23),
% 2.09/0.65    inference(avatar_split_clause,[],[f225,f216,f234,f230])).
% 2.09/0.65  fof(f230,plain,(
% 2.09/0.65    spl7_25 <=> k1_xboole_0 = sK4),
% 2.09/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 2.09/0.65  fof(f225,plain,(
% 2.09/0.65    k1_xboole_0 != k1_relat_1(sK4) | k1_xboole_0 = sK4 | ~spl7_23),
% 2.09/0.65    inference(resolution,[],[f218,f72])).
% 2.09/0.65  fof(f72,plain,(
% 2.09/0.65    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 2.09/0.65    inference(cnf_transformation,[],[f31])).
% 2.09/0.65  fof(f31,plain,(
% 2.09/0.65    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.09/0.65    inference(flattening,[],[f30])).
% 2.09/0.65  fof(f30,plain,(
% 2.09/0.65    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.09/0.65    inference(ennf_transformation,[],[f9])).
% 2.09/0.65  fof(f9,axiom,(
% 2.09/0.65    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.09/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 2.09/0.65  fof(f224,plain,(
% 2.09/0.65    spl7_24 | ~spl7_11),
% 2.09/0.65    inference(avatar_split_clause,[],[f214,f154,f221])).
% 2.09/0.65  fof(f214,plain,(
% 2.09/0.65    v1_relat_1(sK5) | ~spl7_11),
% 2.09/0.65    inference(resolution,[],[f89,f156])).
% 2.09/0.65  fof(f89,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f46])).
% 2.09/0.65  fof(f46,plain,(
% 2.09/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.65    inference(ennf_transformation,[],[f13])).
% 2.09/0.65  fof(f13,axiom,(
% 2.09/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.09/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.09/0.65  fof(f219,plain,(
% 2.09/0.65    spl7_23 | ~spl7_8),
% 2.09/0.65    inference(avatar_split_clause,[],[f213,f139,f216])).
% 2.09/0.65  fof(f213,plain,(
% 2.09/0.65    v1_relat_1(sK4) | ~spl7_8),
% 2.09/0.65    inference(resolution,[],[f89,f141])).
% 2.09/0.65  fof(f190,plain,(
% 2.09/0.65    spl7_18),
% 2.09/0.65    inference(avatar_split_clause,[],[f66,f187])).
% 2.09/0.65  fof(f66,plain,(
% 2.09/0.65    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.09/0.65    inference(cnf_transformation,[],[f8])).
% 2.09/0.65  fof(f8,axiom,(
% 2.09/0.65    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.09/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 2.09/0.65  fof(f180,plain,(
% 2.09/0.65    ~spl7_14 | ~spl7_15 | ~spl7_16),
% 2.09/0.65    inference(avatar_split_clause,[],[f52,f177,f173,f169])).
% 2.09/0.65  fof(f52,plain,(
% 2.09/0.65    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 2.09/0.65    inference(cnf_transformation,[],[f26])).
% 2.09/0.65  fof(f26,plain,(
% 2.09/0.65    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.09/0.65    inference(flattening,[],[f25])).
% 2.09/0.65  fof(f25,plain,(
% 2.09/0.65    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.09/0.65    inference(ennf_transformation,[],[f22])).
% 2.09/0.65  fof(f22,negated_conjecture,(
% 2.09/0.65    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 2.09/0.65    inference(negated_conjecture,[],[f21])).
% 2.09/0.65  fof(f21,conjecture,(
% 2.09/0.65    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 2.09/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 2.09/0.65  fof(f167,plain,(
% 2.09/0.65    spl7_13),
% 2.09/0.65    inference(avatar_split_clause,[],[f53,f164])).
% 2.09/0.65  fof(f53,plain,(
% 2.09/0.65    v1_funct_1(sK5)),
% 2.09/0.65    inference(cnf_transformation,[],[f26])).
% 2.09/0.65  fof(f162,plain,(
% 2.09/0.65    spl7_12),
% 2.09/0.65    inference(avatar_split_clause,[],[f54,f159])).
% 2.09/0.65  fof(f54,plain,(
% 2.09/0.65    v1_funct_2(sK5,sK3,sK1)),
% 2.09/0.65    inference(cnf_transformation,[],[f26])).
% 2.09/0.65  fof(f157,plain,(
% 2.09/0.65    spl7_11),
% 2.09/0.65    inference(avatar_split_clause,[],[f55,f154])).
% 2.09/0.65  fof(f55,plain,(
% 2.09/0.65    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.09/0.65    inference(cnf_transformation,[],[f26])).
% 2.09/0.65  fof(f152,plain,(
% 2.09/0.65    spl7_10),
% 2.09/0.65    inference(avatar_split_clause,[],[f56,f149])).
% 2.09/0.65  fof(f56,plain,(
% 2.09/0.65    v1_funct_1(sK4)),
% 2.09/0.65    inference(cnf_transformation,[],[f26])).
% 2.09/0.65  fof(f147,plain,(
% 2.09/0.65    spl7_9),
% 2.09/0.65    inference(avatar_split_clause,[],[f57,f144])).
% 2.09/0.65  fof(f57,plain,(
% 2.09/0.65    v1_funct_2(sK4,sK2,sK1)),
% 2.09/0.65    inference(cnf_transformation,[],[f26])).
% 2.09/0.65  fof(f142,plain,(
% 2.09/0.65    spl7_8),
% 2.09/0.65    inference(avatar_split_clause,[],[f58,f139])).
% 2.09/0.65  fof(f58,plain,(
% 2.09/0.65    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.09/0.65    inference(cnf_transformation,[],[f26])).
% 2.09/0.65  fof(f137,plain,(
% 2.09/0.65    ~spl7_7),
% 2.09/0.65    inference(avatar_split_clause,[],[f59,f134])).
% 2.09/0.65  fof(f59,plain,(
% 2.09/0.65    ~v1_xboole_0(sK3)),
% 2.09/0.65    inference(cnf_transformation,[],[f26])).
% 2.09/0.65  fof(f132,plain,(
% 2.09/0.65    spl7_6),
% 2.09/0.65    inference(avatar_split_clause,[],[f60,f129])).
% 2.09/0.65  fof(f60,plain,(
% 2.09/0.65    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.09/0.65    inference(cnf_transformation,[],[f26])).
% 2.09/0.65  fof(f127,plain,(
% 2.09/0.65    spl7_5),
% 2.09/0.65    inference(avatar_split_clause,[],[f61,f124])).
% 2.09/0.65  fof(f61,plain,(
% 2.09/0.65    r1_subset_1(sK2,sK3)),
% 2.09/0.65    inference(cnf_transformation,[],[f26])).
% 2.09/0.65  fof(f122,plain,(
% 2.09/0.65    ~spl7_4),
% 2.09/0.65    inference(avatar_split_clause,[],[f62,f119])).
% 2.09/0.65  fof(f62,plain,(
% 2.09/0.65    ~v1_xboole_0(sK2)),
% 2.09/0.65    inference(cnf_transformation,[],[f26])).
% 2.09/0.65  fof(f117,plain,(
% 2.09/0.65    spl7_3),
% 2.09/0.65    inference(avatar_split_clause,[],[f63,f114])).
% 2.09/0.65  fof(f63,plain,(
% 2.09/0.65    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.09/0.65    inference(cnf_transformation,[],[f26])).
% 2.09/0.65  fof(f112,plain,(
% 2.09/0.65    ~spl7_2),
% 2.09/0.65    inference(avatar_split_clause,[],[f64,f109])).
% 2.09/0.65  fof(f64,plain,(
% 2.09/0.65    ~v1_xboole_0(sK1)),
% 2.09/0.65    inference(cnf_transformation,[],[f26])).
% 2.09/0.65  fof(f107,plain,(
% 2.09/0.65    ~spl7_1),
% 2.09/0.65    inference(avatar_split_clause,[],[f65,f104])).
% 2.09/0.65  fof(f65,plain,(
% 2.09/0.65    ~v1_xboole_0(sK0)),
% 2.09/0.65    inference(cnf_transformation,[],[f26])).
% 2.09/0.65  % SZS output end Proof for theBenchmark
% 2.09/0.65  % (8238)------------------------------
% 2.09/0.65  % (8238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.65  % (8238)Termination reason: Refutation
% 2.09/0.65  
% 2.09/0.65  % (8238)Memory used [KB]: 12025
% 2.09/0.65  % (8238)Time elapsed: 0.208 s
% 2.09/0.65  % (8238)------------------------------
% 2.09/0.65  % (8238)------------------------------
% 2.09/0.65  % (8221)Success in time 0.287 s
%------------------------------------------------------------------------------
