%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:28 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  325 ( 731 expanded)
%              Number of leaves         :   77 ( 359 expanded)
%              Depth                    :   14
%              Number of atoms          : 1547 (3333 expanded)
%              Number of equality atoms :  184 ( 492 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1628,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f165,f178,f183,f188,f217,f222,f237,f242,f262,f269,f355,f360,f366,f372,f376,f382,f397,f413,f433,f456,f464,f472,f484,f495,f496,f508,f523,f552,f611,f639,f669,f681,f708,f713,f766,f787,f795,f831,f837,f899,f942,f973,f986,f1541,f1549,f1627])).

fof(f1627,plain,
    ( ~ spl6_91
    | ~ spl6_6
    | spl6_16
    | ~ spl6_30
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_124 ),
    inference(avatar_split_clause,[],[f1626,f983,f374,f370,f266,f175,f127,f705])).

fof(f705,plain,
    ( spl6_91
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f127,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f175,plain,
    ( spl6_16
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f266,plain,
    ( spl6_30
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f370,plain,
    ( spl6_41
  <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f374,plain,
    ( spl6_42
  <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f983,plain,
    ( spl6_124
  <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_124])])).

fof(f1626,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_6
    | spl6_16
    | ~ spl6_30
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_124 ),
    inference(forward_demodulation,[],[f1625,f985])).

fof(f985,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_124 ),
    inference(avatar_component_clause,[],[f983])).

fof(f1625,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_6
    | spl6_16
    | ~ spl6_30
    | ~ spl6_41
    | ~ spl6_42 ),
    inference(forward_demodulation,[],[f1624,f371])).

fof(f371,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f370])).

fof(f1624,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl6_6
    | spl6_16
    | ~ spl6_30
    | ~ spl6_42 ),
    inference(forward_demodulation,[],[f1623,f268])).

fof(f268,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f266])).

fof(f1623,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl6_6
    | spl6_16
    | ~ spl6_42 ),
    inference(forward_demodulation,[],[f1622,f318])).

fof(f318,plain,
    ( ! [X1] : k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))
    | ~ spl6_6 ),
    inference(resolution,[],[f95,f129])).

fof(f129,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f86,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f1622,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_16
    | ~ spl6_42 ),
    inference(forward_demodulation,[],[f177,f375])).

fof(f375,plain,
    ( ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f374])).

fof(f177,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f175])).

fof(f1549,plain,
    ( spl6_14
    | spl6_1
    | ~ spl6_107
    | ~ spl6_101
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_6
    | spl6_7
    | ~ spl6_3
    | spl6_4
    | spl6_2
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_91
    | ~ spl6_116
    | ~ spl6_124 ),
    inference(avatar_split_clause,[],[f1548,f983,f896,f705,f374,f370,f266,f127,f107,f117,f112,f132,f127,f147,f142,f137,f162,f157,f152,f784,f828,f102,f167])).

fof(f167,plain,
    ( spl6_14
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f102,plain,
    ( spl6_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f828,plain,
    ( spl6_107
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).

fof(f784,plain,
    ( spl6_101
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).

fof(f152,plain,
    ( spl6_11
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f157,plain,
    ( spl6_12
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f162,plain,
    ( spl6_13
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f137,plain,
    ( spl6_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f142,plain,
    ( spl6_9
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f147,plain,
    ( spl6_10
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f132,plain,
    ( spl6_7
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f112,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f117,plain,
    ( spl6_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f107,plain,
    ( spl6_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f896,plain,
    ( spl6_116
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).

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
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_91
    | ~ spl6_116
    | ~ spl6_124 ),
    inference(trivial_inequality_removal,[],[f1547])).

fof(f1547,plain,
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
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_91
    | ~ spl6_116
    | ~ spl6_124 ),
    inference(forward_demodulation,[],[f1546,f707])).

fof(f707,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_91 ),
    inference(avatar_component_clause,[],[f705])).

fof(f1546,plain,
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
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_116
    | ~ spl6_124 ),
    inference(forward_demodulation,[],[f1545,f985])).

fof(f1545,plain,
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
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_116 ),
    inference(forward_demodulation,[],[f1544,f371])).

fof(f1544,plain,
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
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_42
    | ~ spl6_116 ),
    inference(forward_demodulation,[],[f1543,f268])).

fof(f1543,plain,
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
    | ~ spl6_6
    | ~ spl6_42
    | ~ spl6_116 ),
    inference(forward_demodulation,[],[f1542,f318])).

fof(f1542,plain,
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
    | ~ spl6_42
    | ~ spl6_116 ),
    inference(forward_demodulation,[],[f1518,f375])).

fof(f1518,plain,
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
    | ~ spl6_116 ),
    inference(resolution,[],[f898,f98])).

fof(f98,plain,(
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
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).

fof(f898,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_116 ),
    inference(avatar_component_clause,[],[f896])).

fof(f1541,plain,
    ( spl6_15
    | spl6_1
    | ~ spl6_107
    | ~ spl6_101
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_6
    | spl6_7
    | ~ spl6_3
    | spl6_4
    | spl6_2
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_91
    | ~ spl6_116
    | ~ spl6_124 ),
    inference(avatar_split_clause,[],[f1540,f983,f896,f705,f374,f370,f266,f127,f107,f117,f112,f132,f127,f147,f142,f137,f162,f157,f152,f784,f828,f102,f171])).

fof(f171,plain,
    ( spl6_15
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f1540,plain,
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
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_91
    | ~ spl6_116
    | ~ spl6_124 ),
    inference(trivial_inequality_removal,[],[f1539])).

fof(f1539,plain,
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
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_91
    | ~ spl6_116
    | ~ spl6_124 ),
    inference(forward_demodulation,[],[f1538,f707])).

fof(f1538,plain,
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
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_116
    | ~ spl6_124 ),
    inference(forward_demodulation,[],[f1537,f985])).

fof(f1537,plain,
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
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_116 ),
    inference(forward_demodulation,[],[f1536,f371])).

fof(f1536,plain,
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
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_42
    | ~ spl6_116 ),
    inference(forward_demodulation,[],[f1535,f268])).

fof(f1535,plain,
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
    | ~ spl6_6
    | ~ spl6_42
    | ~ spl6_116 ),
    inference(forward_demodulation,[],[f1534,f318])).

fof(f1534,plain,
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
    | ~ spl6_42
    | ~ spl6_116 ),
    inference(forward_demodulation,[],[f1517,f375])).

fof(f1517,plain,
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
    | ~ spl6_116 ),
    inference(resolution,[],[f898,f99])).

fof(f99,plain,(
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
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f986,plain,
    ( spl6_124
    | ~ spl6_56
    | ~ spl6_123 ),
    inference(avatar_split_clause,[],[f978,f970,f454,f983])).

fof(f454,plain,
    ( spl6_56
  <=> ! [X0] :
        ( ~ r1_xboole_0(sK3,X0)
        | k1_xboole_0 = k7_relat_1(sK5,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f970,plain,
    ( spl6_123
  <=> r1_xboole_0(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_123])])).

fof(f978,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_56
    | ~ spl6_123 ),
    inference(resolution,[],[f972,f455])).

fof(f455,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK3,X0)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f454])).

fof(f972,plain,
    ( r1_xboole_0(sK3,k1_xboole_0)
    | ~ spl6_123 ),
    inference(avatar_component_clause,[],[f970])).

fof(f973,plain,
    ( spl6_123
    | ~ spl6_24
    | ~ spl6_43
    | ~ spl6_119 ),
    inference(avatar_split_clause,[],[f958,f939,f379,f219,f970])).

fof(f219,plain,
    ( spl6_24
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f379,plain,
    ( spl6_43
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f939,plain,
    ( spl6_119
  <=> k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_119])])).

fof(f958,plain,
    ( r1_xboole_0(sK3,k1_xboole_0)
    | ~ spl6_24
    | ~ spl6_43
    | ~ spl6_119 ),
    inference(trivial_inequality_removal,[],[f957])).

fof(f957,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK3,k1_xboole_0)
    | ~ spl6_24
    | ~ spl6_43
    | ~ spl6_119 ),
    inference(superposition,[],[f442,f941])).

fof(f941,plain,
    ( k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0)
    | ~ spl6_119 ),
    inference(avatar_component_clause,[],[f939])).

fof(f442,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k9_relat_1(sK5,X1)
        | r1_xboole_0(sK3,X1) )
    | ~ spl6_24
    | ~ spl6_43 ),
    inference(backward_demodulation,[],[f295,f381])).

fof(f381,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f379])).

fof(f295,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k9_relat_1(sK5,X1)
        | r1_xboole_0(k1_relat_1(sK5),X1) )
    | ~ spl6_24 ),
    inference(resolution,[],[f77,f221])).

fof(f221,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f219])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f942,plain,
    ( spl6_119
    | ~ spl6_66
    | ~ spl6_102
    | ~ spl6_108 ),
    inference(avatar_split_clause,[],[f937,f834,f792,f520,f939])).

fof(f520,plain,
    ( spl6_66
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f792,plain,
    ( spl6_102
  <=> k9_relat_1(sK5,k1_xboole_0) = k9_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).

fof(f834,plain,
    ( spl6_108
  <=> k1_xboole_0 = k7_relat_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_108])])).

fof(f937,plain,
    ( k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0)
    | ~ spl6_66
    | ~ spl6_102
    | ~ spl6_108 ),
    inference(forward_demodulation,[],[f936,f522])).

fof(f522,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f520])).

fof(f936,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0)
    | ~ spl6_102
    | ~ spl6_108 ),
    inference(forward_demodulation,[],[f794,f836])).

fof(f836,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl6_108 ),
    inference(avatar_component_clause,[],[f834])).

fof(f794,plain,
    ( k9_relat_1(sK5,k1_xboole_0) = k9_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0)
    | ~ spl6_102 ),
    inference(avatar_component_clause,[],[f792])).

fof(f899,plain,
    ( spl6_116
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_83 ),
    inference(avatar_split_clause,[],[f894,f637,f137,f142,f147,f896])).

fof(f637,plain,
    ( spl6_83
  <=> ! [X1] :
        ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f894,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_8
    | ~ spl6_83 ),
    inference(resolution,[],[f638,f139])).

fof(f139,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f638,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) )
    | ~ spl6_83 ),
    inference(avatar_component_clause,[],[f637])).

fof(f837,plain,
    ( spl6_108
    | ~ spl6_29
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f832,f462,f259,f834])).

fof(f259,plain,
    ( spl6_29
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f462,plain,
    ( spl6_58
  <=> ! [X2] :
        ( ~ r1_xboole_0(X2,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f832,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl6_29
    | ~ spl6_58 ),
    inference(resolution,[],[f463,f261])).

fof(f261,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f259])).

fof(f463,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X2) )
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f462])).

fof(f831,plain,
    ( spl6_107
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f826,f609,f137,f142,f147,f828])).

fof(f609,plain,
    ( spl6_78
  <=> ! [X1] :
        ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f826,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_8
    | ~ spl6_78 ),
    inference(resolution,[],[f610,f139])).

fof(f610,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) )
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f609])).

fof(f795,plain,
    ( spl6_102
    | ~ spl6_24
    | ~ spl6_98 ),
    inference(avatar_split_clause,[],[f789,f763,f219,f792])).

fof(f763,plain,
    ( spl6_98
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f789,plain,
    ( k9_relat_1(sK5,k1_xboole_0) = k9_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0)
    | ~ spl6_24
    | ~ spl6_98 ),
    inference(resolution,[],[f765,f322])).

fof(f322,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k9_relat_1(k7_relat_1(sK5,X3),X2) = k9_relat_1(sK5,X2) )
    | ~ spl6_24 ),
    inference(resolution,[],[f70,f221])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f765,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl6_98 ),
    inference(avatar_component_clause,[],[f763])).

fof(f787,plain,
    ( spl6_101
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_69 ),
    inference(avatar_split_clause,[],[f782,f550,f137,f142,f147,f784])).

fof(f550,plain,
    ( spl6_69
  <=> ! [X1] :
        ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f782,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_8
    | ~ spl6_69 ),
    inference(resolution,[],[f551,f139])).

fof(f551,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) )
    | ~ spl6_69 ),
    inference(avatar_component_clause,[],[f550])).

fof(f766,plain,
    ( spl6_98
    | ~ spl6_18
    | ~ spl6_32
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f761,f710,f276,f185,f763])).

fof(f185,plain,
    ( spl6_18
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f276,plain,
    ( spl6_32
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f710,plain,
    ( spl6_92
  <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f761,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl6_18
    | ~ spl6_32
    | ~ spl6_92 ),
    inference(forward_demodulation,[],[f753,f187])).

fof(f187,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f185])).

fof(f753,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK2)
    | ~ spl6_32
    | ~ spl6_92 ),
    inference(superposition,[],[f513,f712])).

fof(f712,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,sK2)
    | ~ spl6_92 ),
    inference(avatar_component_clause,[],[f710])).

fof(f513,plain,
    ( ! [X4] : r1_tarski(k1_relat_1(k7_relat_1(k1_xboole_0,X4)),X4)
    | ~ spl6_32 ),
    inference(resolution,[],[f277,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f277,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f276])).

fof(f713,plain,
    ( spl6_92
    | ~ spl6_65
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f701,f678,f506,f710])).

fof(f506,plain,
    ( spl6_65
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f678,plain,
    ( spl6_88
  <=> r1_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f701,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,sK2)
    | ~ spl6_65
    | ~ spl6_88 ),
    inference(resolution,[],[f680,f507])).

fof(f507,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) )
    | ~ spl6_65 ),
    inference(avatar_component_clause,[],[f506])).

fof(f680,plain,
    ( r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl6_88 ),
    inference(avatar_component_clause,[],[f678])).

fof(f708,plain,
    ( spl6_91
    | ~ spl6_45
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f700,f678,f395,f705])).

fof(f395,plain,
    ( spl6_45
  <=> ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | k1_xboole_0 = k7_relat_1(sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f700,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_45
    | ~ spl6_88 ),
    inference(resolution,[],[f680,f396])).

fof(f396,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f395])).

fof(f681,plain,
    ( spl6_88
    | ~ spl6_23
    | ~ spl6_40
    | ~ spl6_86 ),
    inference(avatar_split_clause,[],[f676,f666,f363,f214,f678])).

fof(f214,plain,
    ( spl6_23
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f363,plain,
    ( spl6_40
  <=> sK2 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f666,plain,
    ( spl6_86
  <=> k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f676,plain,
    ( r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl6_23
    | ~ spl6_40
    | ~ spl6_86 ),
    inference(trivial_inequality_removal,[],[f675])).

fof(f675,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl6_23
    | ~ spl6_40
    | ~ spl6_86 ),
    inference(superposition,[],[f383,f668])).

fof(f668,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0)
    | ~ spl6_86 ),
    inference(avatar_component_clause,[],[f666])).

fof(f383,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK4,X0)
        | r1_xboole_0(sK2,X0) )
    | ~ spl6_23
    | ~ spl6_40 ),
    inference(backward_demodulation,[],[f294,f365])).

fof(f365,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f363])).

fof(f294,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK4,X0)
        | r1_xboole_0(k1_relat_1(sK4),X0) )
    | ~ spl6_23 ),
    inference(resolution,[],[f77,f216])).

fof(f216,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f214])).

fof(f669,plain,
    ( spl6_86
    | ~ spl6_23
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f664,f520,f492,f481,f214,f666])).

fof(f481,plain,
    ( spl6_61
  <=> k1_xboole_0 = k7_relat_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f492,plain,
    ( spl6_62
  <=> r1_tarski(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f664,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0)
    | ~ spl6_23
    | ~ spl6_61
    | ~ spl6_62
    | ~ spl6_66 ),
    inference(forward_demodulation,[],[f663,f522])).

fof(f663,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0)
    | ~ spl6_23
    | ~ spl6_61
    | ~ spl6_62 ),
    inference(forward_demodulation,[],[f661,f483])).

fof(f483,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f481])).

fof(f661,plain,
    ( k9_relat_1(sK4,k1_xboole_0) = k9_relat_1(k7_relat_1(sK4,sK3),k1_xboole_0)
    | ~ spl6_23
    | ~ spl6_62 ),
    inference(resolution,[],[f321,f494])).

fof(f494,plain,
    ( r1_tarski(k1_xboole_0,sK3)
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f492])).

fof(f321,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k9_relat_1(sK4,X0) = k9_relat_1(k7_relat_1(sK4,X1),X0) )
    | ~ spl6_23 ),
    inference(resolution,[],[f70,f216])).

fof(f639,plain,
    ( ~ spl6_6
    | ~ spl6_12
    | spl6_7
    | ~ spl6_13
    | spl6_2
    | spl6_83
    | ~ spl6_11
    | ~ spl6_59 ),
    inference(avatar_split_clause,[],[f631,f470,f152,f637,f107,f162,f132,f157,f127])).

fof(f470,plain,
    ( spl6_59
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f631,plain,
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
    | ~ spl6_11
    | ~ spl6_59 ),
    inference(resolution,[],[f471,f154])).

fof(f154,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f152])).

fof(f471,plain,
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
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f470])).

fof(f611,plain,
    ( ~ spl6_6
    | ~ spl6_12
    | spl6_7
    | ~ spl6_13
    | spl6_2
    | spl6_78
    | ~ spl6_11
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f603,f431,f152,f609,f107,f162,f132,f157,f127])).

fof(f431,plain,
    ( spl6_52
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f603,plain,
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
    | ~ spl6_11
    | ~ spl6_52 ),
    inference(resolution,[],[f432,f154])).

fof(f432,plain,
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
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f431])).

fof(f552,plain,
    ( ~ spl6_6
    | ~ spl6_12
    | spl6_7
    | ~ spl6_13
    | spl6_2
    | spl6_69
    | ~ spl6_11
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f544,f411,f152,f550,f107,f162,f132,f157,f127])).

fof(f411,plain,
    ( spl6_48
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f544,plain,
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
    | ~ spl6_11
    | ~ spl6_48 ),
    inference(resolution,[],[f412,f154])).

fof(f412,plain,
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
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f411])).

fof(f523,plain,
    ( spl6_66
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f518,f276,f185,f180,f520])).

fof(f180,plain,
    ( spl6_17
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f518,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f517,f182])).

fof(f182,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f180])).

fof(f517,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_18
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f512,f187])).

fof(f512,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl6_32 ),
    inference(resolution,[],[f277,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f508,plain,
    ( ~ spl6_32
    | spl6_65
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f284,f185,f506,f276])).

fof(f284,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0)
        | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) )
    | ~ spl6_18 ),
    inference(superposition,[],[f69,f187])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f496,plain,
    ( spl6_32
    | ~ spl6_23
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f489,f481,f214,f276])).

fof(f489,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_23
    | ~ spl6_61 ),
    inference(superposition,[],[f225,f483])).

fof(f225,plain,
    ( ! [X1] : v1_relat_1(k7_relat_1(sK4,X1))
    | ~ spl6_23 ),
    inference(resolution,[],[f216,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f495,plain,
    ( spl6_62
    | ~ spl6_18
    | ~ spl6_23
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f490,f481,f214,f185,f492])).

fof(f490,plain,
    ( r1_tarski(k1_xboole_0,sK3)
    | ~ spl6_18
    | ~ spl6_23
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f488,f187])).

fof(f488,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK3)
    | ~ spl6_23
    | ~ spl6_61 ),
    inference(superposition,[],[f224,f483])).

fof(f224,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0)
    | ~ spl6_23 ),
    inference(resolution,[],[f216,f75])).

fof(f484,plain,
    ( spl6_61
    | ~ spl6_29
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f479,f395,f259,f481])).

fof(f479,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl6_29
    | ~ spl6_45 ),
    inference(resolution,[],[f396,f261])).

fof(f472,plain,
    ( spl6_1
    | spl6_4
    | spl6_59
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f465,f112,f470,f117,f102])).

fof(f465,plain,
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
    | ~ spl6_3 ),
    inference(resolution,[],[f92,f114])).

fof(f114,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f112])).

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
      | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(f464,plain,
    ( ~ spl6_24
    | spl6_58
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f446,f379,f462,f219])).

fof(f446,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK3)
        | ~ v1_relat_1(sK5)
        | k1_xboole_0 = k7_relat_1(sK5,X2) )
    | ~ spl6_43 ),
    inference(superposition,[],[f69,f381])).

fof(f456,plain,
    ( ~ spl6_24
    | spl6_56
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f444,f379,f454,f219])).

fof(f444,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK3,X0)
        | ~ v1_relat_1(sK5)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl6_43 ),
    inference(superposition,[],[f78,f381])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f433,plain,
    ( spl6_1
    | spl6_4
    | spl6_52
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f426,f112,f431,f117,f102])).

fof(f426,plain,
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
    | ~ spl6_3 ),
    inference(resolution,[],[f91,f114])).

fof(f91,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f413,plain,
    ( spl6_1
    | spl6_4
    | spl6_48
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f406,f112,f411,f117,f102])).

fof(f406,plain,
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
    | ~ spl6_3 ),
    inference(resolution,[],[f90,f114])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f397,plain,
    ( ~ spl6_23
    | spl6_45
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f385,f363,f395,f214])).

fof(f385,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | ~ v1_relat_1(sK4)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl6_40 ),
    inference(superposition,[],[f78,f365])).

fof(f382,plain,
    ( ~ spl6_24
    | spl6_43
    | ~ spl6_27
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f377,f357,f239,f379,f219])).

fof(f239,plain,
    ( spl6_27
  <=> v4_relat_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f357,plain,
    ( spl6_39
  <=> v1_partfun1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f377,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl6_39 ),
    inference(resolution,[],[f359,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f359,plain,
    ( v1_partfun1(sK5,sK3)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f357])).

fof(f376,plain,
    ( spl6_42
    | ~ spl6_13
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f368,f152,f162,f374])).

fof(f368,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK5)
        | k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) )
    | ~ spl6_11 ),
    inference(resolution,[],[f89,f154])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f372,plain,
    ( spl6_41
    | ~ spl6_10
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f367,f137,f147,f370])).

fof(f367,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) )
    | ~ spl6_8 ),
    inference(resolution,[],[f89,f139])).

fof(f366,plain,
    ( ~ spl6_23
    | spl6_40
    | ~ spl6_26
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f361,f352,f234,f363,f214])).

fof(f234,plain,
    ( spl6_26
  <=> v4_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f352,plain,
    ( spl6_38
  <=> v1_partfun1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f361,plain,
    ( ~ v4_relat_1(sK4,sK2)
    | sK2 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl6_38 ),
    inference(resolution,[],[f354,f83])).

fof(f354,plain,
    ( v1_partfun1(sK4,sK2)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f352])).

fof(f360,plain,
    ( spl6_39
    | ~ spl6_12
    | ~ spl6_13
    | spl6_2
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f350,f152,f107,f162,f157,f357])).

fof(f350,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f73,f154])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f355,plain,
    ( spl6_38
    | ~ spl6_9
    | ~ spl6_10
    | spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f349,f137,f107,f147,f142,f352])).

fof(f349,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f73,f139])).

fof(f269,plain,
    ( spl6_30
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f264,f259,f266])).

fof(f264,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl6_29 ),
    inference(resolution,[],[f261,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f85,f72])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f262,plain,
    ( spl6_4
    | spl6_29
    | spl6_7
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f257,f122,f132,f259,f117])).

fof(f122,plain,
    ( spl6_5
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f257,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f81,f124])).

fof(f124,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f242,plain,
    ( spl6_27
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f232,f152,f239])).

fof(f232,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f88,f154])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f237,plain,
    ( spl6_26
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f231,f137,f234])).

fof(f231,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f88,f139])).

fof(f222,plain,
    ( spl6_24
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f212,f152,f219])).

fof(f212,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_11 ),
    inference(resolution,[],[f87,f154])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f217,plain,
    ( spl6_23
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f211,f137,f214])).

fof(f211,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_8 ),
    inference(resolution,[],[f87,f139])).

fof(f188,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f63,f185])).

fof(f63,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f183,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f64,f180])).

fof(f64,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f178,plain,
    ( ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f49,f175,f171,f167])).

fof(f49,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).

fof(f165,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f50,f162])).

fof(f50,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f160,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f51,f157])).

fof(f51,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f155,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f52,f152])).

fof(f52,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f150,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f53,f147])).

fof(f53,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f145,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f54,f142])).

fof(f54,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f140,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f55,f137])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f135,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f56,f132])).

fof(f56,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f130,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f57,f127])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f125,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f58,f122])).

fof(f58,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f120,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f59,f117])).

fof(f59,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f115,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f60,f112])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f110,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f61,f107])).

fof(f61,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f105,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f62,f102])).

fof(f62,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:48:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (13948)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.50  % (13940)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (13932)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (13936)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (13925)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (13927)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (13931)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (13928)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (13926)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (13945)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (13930)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (13929)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (13950)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (13935)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (13949)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (13954)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (13942)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (13946)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (13937)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (13942)Refutation not found, incomplete strategy% (13942)------------------------------
% 0.22/0.55  % (13942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (13942)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (13942)Memory used [KB]: 10746
% 0.22/0.55  % (13942)Time elapsed: 0.137 s
% 0.22/0.55  % (13942)------------------------------
% 0.22/0.55  % (13942)------------------------------
% 0.22/0.55  % (13941)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (13939)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (13952)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (13943)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (13938)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (13933)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (13947)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (13951)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.52/0.56  % (13934)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.52/0.57  % (13953)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.52/0.57  % (13944)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.67/0.59  % (13947)Refutation not found, incomplete strategy% (13947)------------------------------
% 1.67/0.59  % (13947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.60  % (13935)Refutation not found, incomplete strategy% (13935)------------------------------
% 1.67/0.60  % (13935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.60  % (13935)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.60  
% 1.67/0.60  % (13935)Memory used [KB]: 11513
% 1.67/0.60  % (13935)Time elapsed: 0.176 s
% 1.67/0.60  % (13935)------------------------------
% 1.67/0.60  % (13935)------------------------------
% 1.67/0.61  % (13947)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.61  
% 1.67/0.61  % (13947)Memory used [KB]: 11513
% 1.67/0.61  % (13947)Time elapsed: 0.157 s
% 1.67/0.61  % (13947)------------------------------
% 1.67/0.61  % (13947)------------------------------
% 2.02/0.63  % (13941)Refutation found. Thanks to Tanya!
% 2.02/0.63  % SZS status Theorem for theBenchmark
% 2.02/0.63  % SZS output start Proof for theBenchmark
% 2.02/0.63  fof(f1628,plain,(
% 2.02/0.63    $false),
% 2.02/0.63    inference(avatar_sat_refutation,[],[f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f165,f178,f183,f188,f217,f222,f237,f242,f262,f269,f355,f360,f366,f372,f376,f382,f397,f413,f433,f456,f464,f472,f484,f495,f496,f508,f523,f552,f611,f639,f669,f681,f708,f713,f766,f787,f795,f831,f837,f899,f942,f973,f986,f1541,f1549,f1627])).
% 2.02/0.63  fof(f1627,plain,(
% 2.02/0.63    ~spl6_91 | ~spl6_6 | spl6_16 | ~spl6_30 | ~spl6_41 | ~spl6_42 | ~spl6_124),
% 2.02/0.63    inference(avatar_split_clause,[],[f1626,f983,f374,f370,f266,f175,f127,f705])).
% 2.02/0.63  fof(f705,plain,(
% 2.02/0.63    spl6_91 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).
% 2.02/0.63  fof(f127,plain,(
% 2.02/0.63    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.02/0.63  fof(f175,plain,(
% 2.02/0.63    spl6_16 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 2.02/0.63  fof(f266,plain,(
% 2.02/0.63    spl6_30 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 2.02/0.63  fof(f370,plain,(
% 2.02/0.63    spl6_41 <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 2.02/0.63  fof(f374,plain,(
% 2.02/0.63    spl6_42 <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 2.02/0.63  fof(f983,plain,(
% 2.02/0.63    spl6_124 <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_124])])).
% 2.02/0.63  fof(f1626,plain,(
% 2.02/0.63    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | (~spl6_6 | spl6_16 | ~spl6_30 | ~spl6_41 | ~spl6_42 | ~spl6_124)),
% 2.02/0.63    inference(forward_demodulation,[],[f1625,f985])).
% 2.02/0.63  fof(f985,plain,(
% 2.02/0.63    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | ~spl6_124),
% 2.02/0.63    inference(avatar_component_clause,[],[f983])).
% 2.02/0.63  fof(f1625,plain,(
% 2.02/0.63    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | (~spl6_6 | spl6_16 | ~spl6_30 | ~spl6_41 | ~spl6_42)),
% 2.02/0.63    inference(forward_demodulation,[],[f1624,f371])).
% 2.02/0.63  fof(f371,plain,(
% 2.02/0.63    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl6_41),
% 2.02/0.63    inference(avatar_component_clause,[],[f370])).
% 2.02/0.63  fof(f1624,plain,(
% 2.02/0.63    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (~spl6_6 | spl6_16 | ~spl6_30 | ~spl6_42)),
% 2.02/0.63    inference(forward_demodulation,[],[f1623,f268])).
% 2.02/0.63  fof(f268,plain,(
% 2.02/0.63    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl6_30),
% 2.02/0.63    inference(avatar_component_clause,[],[f266])).
% 2.02/0.63  fof(f1623,plain,(
% 2.02/0.63    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | (~spl6_6 | spl6_16 | ~spl6_42)),
% 2.02/0.63    inference(forward_demodulation,[],[f1622,f318])).
% 2.02/0.63  fof(f318,plain,(
% 2.02/0.63    ( ! [X1] : (k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))) ) | ~spl6_6),
% 2.02/0.63    inference(resolution,[],[f95,f129])).
% 2.02/0.63  fof(f129,plain,(
% 2.02/0.63    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl6_6),
% 2.02/0.63    inference(avatar_component_clause,[],[f127])).
% 2.02/0.63  fof(f95,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 2.02/0.63    inference(definition_unfolding,[],[f86,f72])).
% 2.02/0.63  fof(f72,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f4])).
% 2.02/0.63  fof(f4,axiom,(
% 2.02/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.02/0.63  fof(f86,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f42])).
% 2.02/0.63  fof(f42,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f2])).
% 2.02/0.63  fof(f2,axiom,(
% 2.02/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.02/0.63  fof(f1622,plain,(
% 2.02/0.63    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (spl6_16 | ~spl6_42)),
% 2.02/0.63    inference(forward_demodulation,[],[f177,f375])).
% 2.02/0.63  fof(f375,plain,(
% 2.02/0.63    ( ! [X1] : (k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl6_42),
% 2.02/0.63    inference(avatar_component_clause,[],[f374])).
% 2.02/0.63  fof(f177,plain,(
% 2.02/0.63    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_16),
% 2.02/0.63    inference(avatar_component_clause,[],[f175])).
% 2.02/0.63  fof(f1549,plain,(
% 2.02/0.63    spl6_14 | spl6_1 | ~spl6_107 | ~spl6_101 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_6 | spl6_7 | ~spl6_3 | spl6_4 | spl6_2 | ~spl6_6 | ~spl6_30 | ~spl6_41 | ~spl6_42 | ~spl6_91 | ~spl6_116 | ~spl6_124),
% 2.02/0.63    inference(avatar_split_clause,[],[f1548,f983,f896,f705,f374,f370,f266,f127,f107,f117,f112,f132,f127,f147,f142,f137,f162,f157,f152,f784,f828,f102,f167])).
% 2.02/0.63  fof(f167,plain,(
% 2.02/0.63    spl6_14 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 2.02/0.63  fof(f102,plain,(
% 2.02/0.63    spl6_1 <=> v1_xboole_0(sK0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.02/0.63  fof(f828,plain,(
% 2.02/0.63    spl6_107 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).
% 2.02/0.63  fof(f784,plain,(
% 2.02/0.63    spl6_101 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).
% 2.02/0.63  fof(f152,plain,(
% 2.02/0.63    spl6_11 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 2.02/0.63  fof(f157,plain,(
% 2.02/0.63    spl6_12 <=> v1_funct_2(sK5,sK3,sK1)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 2.02/0.63  fof(f162,plain,(
% 2.02/0.63    spl6_13 <=> v1_funct_1(sK5)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 2.02/0.63  fof(f137,plain,(
% 2.02/0.63    spl6_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.02/0.63  fof(f142,plain,(
% 2.02/0.63    spl6_9 <=> v1_funct_2(sK4,sK2,sK1)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 2.02/0.63  fof(f147,plain,(
% 2.02/0.63    spl6_10 <=> v1_funct_1(sK4)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.02/0.63  fof(f132,plain,(
% 2.02/0.63    spl6_7 <=> v1_xboole_0(sK3)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.02/0.63  fof(f112,plain,(
% 2.02/0.63    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.02/0.63  fof(f117,plain,(
% 2.02/0.63    spl6_4 <=> v1_xboole_0(sK2)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.02/0.63  fof(f107,plain,(
% 2.02/0.63    spl6_2 <=> v1_xboole_0(sK1)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.02/0.63  fof(f896,plain,(
% 2.02/0.63    spl6_116 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).
% 2.02/0.63  fof(f1548,plain,(
% 2.02/0.63    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_30 | ~spl6_41 | ~spl6_42 | ~spl6_91 | ~spl6_116 | ~spl6_124)),
% 2.02/0.63    inference(trivial_inequality_removal,[],[f1547])).
% 2.02/0.63  fof(f1547,plain,(
% 2.02/0.63    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_30 | ~spl6_41 | ~spl6_42 | ~spl6_91 | ~spl6_116 | ~spl6_124)),
% 2.02/0.63    inference(forward_demodulation,[],[f1546,f707])).
% 2.02/0.63  fof(f707,plain,(
% 2.02/0.63    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl6_91),
% 2.02/0.63    inference(avatar_component_clause,[],[f705])).
% 2.02/0.63  fof(f1546,plain,(
% 2.02/0.63    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_30 | ~spl6_41 | ~spl6_42 | ~spl6_116 | ~spl6_124)),
% 2.02/0.63    inference(forward_demodulation,[],[f1545,f985])).
% 2.02/0.63  fof(f1545,plain,(
% 2.02/0.63    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_30 | ~spl6_41 | ~spl6_42 | ~spl6_116)),
% 2.02/0.63    inference(forward_demodulation,[],[f1544,f371])).
% 2.02/0.63  fof(f1544,plain,(
% 2.02/0.63    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_30 | ~spl6_42 | ~spl6_116)),
% 2.02/0.63    inference(forward_demodulation,[],[f1543,f268])).
% 2.02/0.63  fof(f1543,plain,(
% 2.02/0.63    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_42 | ~spl6_116)),
% 2.02/0.63    inference(forward_demodulation,[],[f1542,f318])).
% 2.02/0.63  fof(f1542,plain,(
% 2.02/0.63    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_42 | ~spl6_116)),
% 2.02/0.63    inference(forward_demodulation,[],[f1518,f375])).
% 2.02/0.63  fof(f1518,plain,(
% 2.02/0.63    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~spl6_116),
% 2.02/0.63    inference(resolution,[],[f898,f98])).
% 2.02/0.63  fof(f98,plain,(
% 2.02/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 2.02/0.63    inference(equality_resolution,[],[f66])).
% 2.02/0.63  fof(f66,plain,(
% 2.02/0.63    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 2.02/0.63    inference(cnf_transformation,[],[f27])).
% 2.02/0.63  fof(f27,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.02/0.63    inference(flattening,[],[f26])).
% 2.02/0.63  fof(f26,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f19])).
% 2.02/0.63  fof(f19,axiom,(
% 2.02/0.63    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).
% 2.02/0.63  fof(f898,plain,(
% 2.02/0.63    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl6_116),
% 2.02/0.63    inference(avatar_component_clause,[],[f896])).
% 2.02/0.63  fof(f1541,plain,(
% 2.02/0.63    spl6_15 | spl6_1 | ~spl6_107 | ~spl6_101 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_6 | spl6_7 | ~spl6_3 | spl6_4 | spl6_2 | ~spl6_6 | ~spl6_30 | ~spl6_41 | ~spl6_42 | ~spl6_91 | ~spl6_116 | ~spl6_124),
% 2.02/0.63    inference(avatar_split_clause,[],[f1540,f983,f896,f705,f374,f370,f266,f127,f107,f117,f112,f132,f127,f147,f142,f137,f162,f157,f152,f784,f828,f102,f171])).
% 2.02/0.63  fof(f171,plain,(
% 2.02/0.63    spl6_15 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 2.02/0.63  fof(f1540,plain,(
% 2.02/0.63    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_30 | ~spl6_41 | ~spl6_42 | ~spl6_91 | ~spl6_116 | ~spl6_124)),
% 2.02/0.63    inference(trivial_inequality_removal,[],[f1539])).
% 2.02/0.63  fof(f1539,plain,(
% 2.02/0.63    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_30 | ~spl6_41 | ~spl6_42 | ~spl6_91 | ~spl6_116 | ~spl6_124)),
% 2.02/0.63    inference(forward_demodulation,[],[f1538,f707])).
% 2.02/0.63  fof(f1538,plain,(
% 2.02/0.63    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_30 | ~spl6_41 | ~spl6_42 | ~spl6_116 | ~spl6_124)),
% 2.02/0.63    inference(forward_demodulation,[],[f1537,f985])).
% 2.02/0.63  fof(f1537,plain,(
% 2.02/0.63    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_30 | ~spl6_41 | ~spl6_42 | ~spl6_116)),
% 2.02/0.63    inference(forward_demodulation,[],[f1536,f371])).
% 2.02/0.63  fof(f1536,plain,(
% 2.02/0.63    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_30 | ~spl6_42 | ~spl6_116)),
% 2.02/0.63    inference(forward_demodulation,[],[f1535,f268])).
% 2.02/0.63  fof(f1535,plain,(
% 2.02/0.63    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_42 | ~spl6_116)),
% 2.02/0.63    inference(forward_demodulation,[],[f1534,f318])).
% 2.02/0.63  fof(f1534,plain,(
% 2.02/0.63    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_42 | ~spl6_116)),
% 2.02/0.63    inference(forward_demodulation,[],[f1517,f375])).
% 2.02/0.63  fof(f1517,plain,(
% 2.02/0.63    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~spl6_116),
% 2.02/0.63    inference(resolution,[],[f898,f99])).
% 2.02/0.63  fof(f99,plain,(
% 2.02/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 2.02/0.63    inference(equality_resolution,[],[f65])).
% 2.02/0.63  fof(f65,plain,(
% 2.02/0.63    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 2.02/0.63    inference(cnf_transformation,[],[f27])).
% 2.02/0.63  fof(f986,plain,(
% 2.02/0.63    spl6_124 | ~spl6_56 | ~spl6_123),
% 2.02/0.63    inference(avatar_split_clause,[],[f978,f970,f454,f983])).
% 2.02/0.63  fof(f454,plain,(
% 2.02/0.63    spl6_56 <=> ! [X0] : (~r1_xboole_0(sK3,X0) | k1_xboole_0 = k7_relat_1(sK5,X0))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).
% 2.02/0.63  fof(f970,plain,(
% 2.02/0.63    spl6_123 <=> r1_xboole_0(sK3,k1_xboole_0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_123])])).
% 2.02/0.63  fof(f978,plain,(
% 2.02/0.63    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | (~spl6_56 | ~spl6_123)),
% 2.02/0.63    inference(resolution,[],[f972,f455])).
% 2.02/0.63  fof(f455,plain,(
% 2.02/0.63    ( ! [X0] : (~r1_xboole_0(sK3,X0) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl6_56),
% 2.02/0.63    inference(avatar_component_clause,[],[f454])).
% 2.02/0.63  fof(f972,plain,(
% 2.02/0.63    r1_xboole_0(sK3,k1_xboole_0) | ~spl6_123),
% 2.02/0.63    inference(avatar_component_clause,[],[f970])).
% 2.02/0.63  fof(f973,plain,(
% 2.02/0.63    spl6_123 | ~spl6_24 | ~spl6_43 | ~spl6_119),
% 2.02/0.63    inference(avatar_split_clause,[],[f958,f939,f379,f219,f970])).
% 2.02/0.63  fof(f219,plain,(
% 2.02/0.63    spl6_24 <=> v1_relat_1(sK5)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 2.02/0.63  fof(f379,plain,(
% 2.02/0.63    spl6_43 <=> sK3 = k1_relat_1(sK5)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 2.02/0.63  fof(f939,plain,(
% 2.02/0.63    spl6_119 <=> k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_119])])).
% 2.02/0.63  fof(f958,plain,(
% 2.02/0.63    r1_xboole_0(sK3,k1_xboole_0) | (~spl6_24 | ~spl6_43 | ~spl6_119)),
% 2.02/0.63    inference(trivial_inequality_removal,[],[f957])).
% 2.02/0.63  fof(f957,plain,(
% 2.02/0.63    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK3,k1_xboole_0) | (~spl6_24 | ~spl6_43 | ~spl6_119)),
% 2.02/0.63    inference(superposition,[],[f442,f941])).
% 2.02/0.63  fof(f941,plain,(
% 2.02/0.63    k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0) | ~spl6_119),
% 2.02/0.63    inference(avatar_component_clause,[],[f939])).
% 2.02/0.63  fof(f442,plain,(
% 2.02/0.63    ( ! [X1] : (k1_xboole_0 != k9_relat_1(sK5,X1) | r1_xboole_0(sK3,X1)) ) | (~spl6_24 | ~spl6_43)),
% 2.02/0.63    inference(backward_demodulation,[],[f295,f381])).
% 2.02/0.63  fof(f381,plain,(
% 2.02/0.63    sK3 = k1_relat_1(sK5) | ~spl6_43),
% 2.02/0.63    inference(avatar_component_clause,[],[f379])).
% 2.02/0.63  fof(f295,plain,(
% 2.02/0.63    ( ! [X1] : (k1_xboole_0 != k9_relat_1(sK5,X1) | r1_xboole_0(k1_relat_1(sK5),X1)) ) | ~spl6_24),
% 2.02/0.63    inference(resolution,[],[f77,f221])).
% 2.02/0.63  fof(f221,plain,(
% 2.02/0.63    v1_relat_1(sK5) | ~spl6_24),
% 2.02/0.63    inference(avatar_component_clause,[],[f219])).
% 2.02/0.63  fof(f77,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f36])).
% 2.02/0.63  fof(f36,plain,(
% 2.02/0.63    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.02/0.63    inference(ennf_transformation,[],[f7])).
% 2.02/0.63  fof(f7,axiom,(
% 2.02/0.63    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 2.02/0.63  fof(f942,plain,(
% 2.02/0.63    spl6_119 | ~spl6_66 | ~spl6_102 | ~spl6_108),
% 2.02/0.63    inference(avatar_split_clause,[],[f937,f834,f792,f520,f939])).
% 2.02/0.63  fof(f520,plain,(
% 2.02/0.63    spl6_66 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).
% 2.02/0.63  fof(f792,plain,(
% 2.02/0.63    spl6_102 <=> k9_relat_1(sK5,k1_xboole_0) = k9_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).
% 2.02/0.63  fof(f834,plain,(
% 2.02/0.63    spl6_108 <=> k1_xboole_0 = k7_relat_1(sK5,sK2)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_108])])).
% 2.02/0.63  fof(f937,plain,(
% 2.02/0.63    k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0) | (~spl6_66 | ~spl6_102 | ~spl6_108)),
% 2.02/0.63    inference(forward_demodulation,[],[f936,f522])).
% 2.02/0.63  fof(f522,plain,(
% 2.02/0.63    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | ~spl6_66),
% 2.02/0.63    inference(avatar_component_clause,[],[f520])).
% 2.02/0.63  fof(f936,plain,(
% 2.02/0.63    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0) | (~spl6_102 | ~spl6_108)),
% 2.02/0.63    inference(forward_demodulation,[],[f794,f836])).
% 2.02/0.63  fof(f836,plain,(
% 2.02/0.63    k1_xboole_0 = k7_relat_1(sK5,sK2) | ~spl6_108),
% 2.02/0.63    inference(avatar_component_clause,[],[f834])).
% 2.02/0.63  fof(f794,plain,(
% 2.02/0.63    k9_relat_1(sK5,k1_xboole_0) = k9_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0) | ~spl6_102),
% 2.02/0.63    inference(avatar_component_clause,[],[f792])).
% 2.02/0.63  fof(f899,plain,(
% 2.02/0.63    spl6_116 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_83),
% 2.02/0.63    inference(avatar_split_clause,[],[f894,f637,f137,f142,f147,f896])).
% 2.02/0.63  fof(f637,plain,(
% 2.02/0.63    spl6_83 <=> ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).
% 2.02/0.63  fof(f894,plain,(
% 2.02/0.63    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_8 | ~spl6_83)),
% 2.02/0.63    inference(resolution,[],[f638,f139])).
% 2.02/0.63  fof(f139,plain,(
% 2.02/0.63    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl6_8),
% 2.02/0.63    inference(avatar_component_clause,[],[f137])).
% 2.02/0.63  fof(f638,plain,(
% 2.02/0.63    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))) ) | ~spl6_83),
% 2.02/0.63    inference(avatar_component_clause,[],[f637])).
% 2.02/0.63  fof(f837,plain,(
% 2.02/0.63    spl6_108 | ~spl6_29 | ~spl6_58),
% 2.02/0.63    inference(avatar_split_clause,[],[f832,f462,f259,f834])).
% 2.02/0.63  fof(f259,plain,(
% 2.02/0.63    spl6_29 <=> r1_xboole_0(sK2,sK3)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 2.02/0.63  fof(f462,plain,(
% 2.02/0.63    spl6_58 <=> ! [X2] : (~r1_xboole_0(X2,sK3) | k1_xboole_0 = k7_relat_1(sK5,X2))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 2.02/0.63  fof(f832,plain,(
% 2.02/0.63    k1_xboole_0 = k7_relat_1(sK5,sK2) | (~spl6_29 | ~spl6_58)),
% 2.02/0.63    inference(resolution,[],[f463,f261])).
% 2.02/0.63  fof(f261,plain,(
% 2.02/0.63    r1_xboole_0(sK2,sK3) | ~spl6_29),
% 2.02/0.63    inference(avatar_component_clause,[],[f259])).
% 2.02/0.63  fof(f463,plain,(
% 2.02/0.63    ( ! [X2] : (~r1_xboole_0(X2,sK3) | k1_xboole_0 = k7_relat_1(sK5,X2)) ) | ~spl6_58),
% 2.02/0.63    inference(avatar_component_clause,[],[f462])).
% 2.02/0.63  fof(f831,plain,(
% 2.02/0.63    spl6_107 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_78),
% 2.02/0.63    inference(avatar_split_clause,[],[f826,f609,f137,f142,f147,f828])).
% 2.02/0.63  fof(f609,plain,(
% 2.02/0.63    spl6_78 <=> ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 2.02/0.63  fof(f826,plain,(
% 2.02/0.63    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_8 | ~spl6_78)),
% 2.02/0.63    inference(resolution,[],[f610,f139])).
% 2.02/0.63  fof(f610,plain,(
% 2.02/0.63    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)) ) | ~spl6_78),
% 2.02/0.63    inference(avatar_component_clause,[],[f609])).
% 2.02/0.63  fof(f795,plain,(
% 2.02/0.63    spl6_102 | ~spl6_24 | ~spl6_98),
% 2.02/0.63    inference(avatar_split_clause,[],[f789,f763,f219,f792])).
% 2.02/0.63  fof(f763,plain,(
% 2.02/0.63    spl6_98 <=> r1_tarski(k1_xboole_0,sK2)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).
% 2.02/0.63  fof(f789,plain,(
% 2.02/0.63    k9_relat_1(sK5,k1_xboole_0) = k9_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0) | (~spl6_24 | ~spl6_98)),
% 2.02/0.63    inference(resolution,[],[f765,f322])).
% 2.02/0.63  fof(f322,plain,(
% 2.02/0.63    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k9_relat_1(k7_relat_1(sK5,X3),X2) = k9_relat_1(sK5,X2)) ) | ~spl6_24),
% 2.02/0.63    inference(resolution,[],[f70,f221])).
% 2.02/0.63  fof(f70,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f30])).
% 2.02/0.63  fof(f30,plain,(
% 2.02/0.63    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f8])).
% 2.02/0.63  fof(f8,axiom,(
% 2.02/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 2.02/0.63  fof(f765,plain,(
% 2.02/0.63    r1_tarski(k1_xboole_0,sK2) | ~spl6_98),
% 2.02/0.63    inference(avatar_component_clause,[],[f763])).
% 2.02/0.63  fof(f787,plain,(
% 2.02/0.63    spl6_101 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_69),
% 2.02/0.63    inference(avatar_split_clause,[],[f782,f550,f137,f142,f147,f784])).
% 2.02/0.63  fof(f550,plain,(
% 2.02/0.63    spl6_69 <=> ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).
% 2.02/0.63  fof(f782,plain,(
% 2.02/0.63    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_8 | ~spl6_69)),
% 2.02/0.63    inference(resolution,[],[f551,f139])).
% 2.02/0.63  fof(f551,plain,(
% 2.02/0.63    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))) ) | ~spl6_69),
% 2.02/0.63    inference(avatar_component_clause,[],[f550])).
% 2.02/0.63  fof(f766,plain,(
% 2.02/0.63    spl6_98 | ~spl6_18 | ~spl6_32 | ~spl6_92),
% 2.02/0.63    inference(avatar_split_clause,[],[f761,f710,f276,f185,f763])).
% 2.02/0.63  fof(f185,plain,(
% 2.02/0.63    spl6_18 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 2.02/0.63  fof(f276,plain,(
% 2.02/0.63    spl6_32 <=> v1_relat_1(k1_xboole_0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 2.02/0.63  fof(f710,plain,(
% 2.02/0.63    spl6_92 <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK2)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).
% 2.02/0.63  fof(f761,plain,(
% 2.02/0.63    r1_tarski(k1_xboole_0,sK2) | (~spl6_18 | ~spl6_32 | ~spl6_92)),
% 2.02/0.63    inference(forward_demodulation,[],[f753,f187])).
% 2.02/0.63  fof(f187,plain,(
% 2.02/0.63    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_18),
% 2.02/0.63    inference(avatar_component_clause,[],[f185])).
% 2.02/0.63  fof(f753,plain,(
% 2.02/0.63    r1_tarski(k1_relat_1(k1_xboole_0),sK2) | (~spl6_32 | ~spl6_92)),
% 2.02/0.63    inference(superposition,[],[f513,f712])).
% 2.02/0.63  fof(f712,plain,(
% 2.02/0.63    k1_xboole_0 = k7_relat_1(k1_xboole_0,sK2) | ~spl6_92),
% 2.02/0.63    inference(avatar_component_clause,[],[f710])).
% 2.02/0.63  fof(f513,plain,(
% 2.02/0.63    ( ! [X4] : (r1_tarski(k1_relat_1(k7_relat_1(k1_xboole_0,X4)),X4)) ) | ~spl6_32),
% 2.02/0.63    inference(resolution,[],[f277,f75])).
% 2.02/0.63  fof(f75,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f35])).
% 2.02/0.63  fof(f35,plain,(
% 2.02/0.63    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.02/0.63    inference(ennf_transformation,[],[f11])).
% 2.02/0.63  fof(f11,axiom,(
% 2.02/0.63    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 2.02/0.63  fof(f277,plain,(
% 2.02/0.63    v1_relat_1(k1_xboole_0) | ~spl6_32),
% 2.02/0.63    inference(avatar_component_clause,[],[f276])).
% 2.02/0.63  fof(f713,plain,(
% 2.02/0.63    spl6_92 | ~spl6_65 | ~spl6_88),
% 2.02/0.63    inference(avatar_split_clause,[],[f701,f678,f506,f710])).
% 2.02/0.63  fof(f506,plain,(
% 2.02/0.63    spl6_65 <=> ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 2.02/0.63  fof(f678,plain,(
% 2.02/0.63    spl6_88 <=> r1_xboole_0(sK2,k1_xboole_0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).
% 2.02/0.63  fof(f701,plain,(
% 2.02/0.63    k1_xboole_0 = k7_relat_1(k1_xboole_0,sK2) | (~spl6_65 | ~spl6_88)),
% 2.02/0.63    inference(resolution,[],[f680,f507])).
% 2.02/0.63  fof(f507,plain,(
% 2.02/0.63    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl6_65),
% 2.02/0.63    inference(avatar_component_clause,[],[f506])).
% 2.02/0.63  fof(f680,plain,(
% 2.02/0.63    r1_xboole_0(sK2,k1_xboole_0) | ~spl6_88),
% 2.02/0.63    inference(avatar_component_clause,[],[f678])).
% 2.02/0.63  fof(f708,plain,(
% 2.02/0.63    spl6_91 | ~spl6_45 | ~spl6_88),
% 2.02/0.63    inference(avatar_split_clause,[],[f700,f678,f395,f705])).
% 2.02/0.63  fof(f395,plain,(
% 2.02/0.63    spl6_45 <=> ! [X0] : (~r1_xboole_0(sK2,X0) | k1_xboole_0 = k7_relat_1(sK4,X0))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 2.02/0.63  fof(f700,plain,(
% 2.02/0.63    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | (~spl6_45 | ~spl6_88)),
% 2.02/0.63    inference(resolution,[],[f680,f396])).
% 2.02/0.63  fof(f396,plain,(
% 2.02/0.63    ( ! [X0] : (~r1_xboole_0(sK2,X0) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl6_45),
% 2.02/0.63    inference(avatar_component_clause,[],[f395])).
% 2.02/0.63  fof(f681,plain,(
% 2.02/0.63    spl6_88 | ~spl6_23 | ~spl6_40 | ~spl6_86),
% 2.02/0.63    inference(avatar_split_clause,[],[f676,f666,f363,f214,f678])).
% 2.02/0.63  fof(f214,plain,(
% 2.02/0.63    spl6_23 <=> v1_relat_1(sK4)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 2.02/0.63  fof(f363,plain,(
% 2.02/0.63    spl6_40 <=> sK2 = k1_relat_1(sK4)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 2.02/0.63  fof(f666,plain,(
% 2.02/0.63    spl6_86 <=> k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).
% 2.02/0.63  fof(f676,plain,(
% 2.02/0.63    r1_xboole_0(sK2,k1_xboole_0) | (~spl6_23 | ~spl6_40 | ~spl6_86)),
% 2.02/0.63    inference(trivial_inequality_removal,[],[f675])).
% 2.02/0.63  fof(f675,plain,(
% 2.02/0.63    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK2,k1_xboole_0) | (~spl6_23 | ~spl6_40 | ~spl6_86)),
% 2.02/0.63    inference(superposition,[],[f383,f668])).
% 2.02/0.63  fof(f668,plain,(
% 2.02/0.63    k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0) | ~spl6_86),
% 2.02/0.63    inference(avatar_component_clause,[],[f666])).
% 2.02/0.63  fof(f383,plain,(
% 2.02/0.63    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK4,X0) | r1_xboole_0(sK2,X0)) ) | (~spl6_23 | ~spl6_40)),
% 2.02/0.63    inference(backward_demodulation,[],[f294,f365])).
% 2.02/0.63  fof(f365,plain,(
% 2.02/0.63    sK2 = k1_relat_1(sK4) | ~spl6_40),
% 2.02/0.63    inference(avatar_component_clause,[],[f363])).
% 2.02/0.63  fof(f294,plain,(
% 2.02/0.63    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK4,X0) | r1_xboole_0(k1_relat_1(sK4),X0)) ) | ~spl6_23),
% 2.02/0.63    inference(resolution,[],[f77,f216])).
% 2.02/0.63  fof(f216,plain,(
% 2.02/0.63    v1_relat_1(sK4) | ~spl6_23),
% 2.02/0.63    inference(avatar_component_clause,[],[f214])).
% 2.02/0.63  fof(f669,plain,(
% 2.02/0.63    spl6_86 | ~spl6_23 | ~spl6_61 | ~spl6_62 | ~spl6_66),
% 2.02/0.63    inference(avatar_split_clause,[],[f664,f520,f492,f481,f214,f666])).
% 2.02/0.63  fof(f481,plain,(
% 2.02/0.63    spl6_61 <=> k1_xboole_0 = k7_relat_1(sK4,sK3)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 2.02/0.63  fof(f492,plain,(
% 2.02/0.63    spl6_62 <=> r1_tarski(k1_xboole_0,sK3)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 2.02/0.63  fof(f664,plain,(
% 2.02/0.63    k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0) | (~spl6_23 | ~spl6_61 | ~spl6_62 | ~spl6_66)),
% 2.02/0.63    inference(forward_demodulation,[],[f663,f522])).
% 2.02/0.63  fof(f663,plain,(
% 2.02/0.63    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0) | (~spl6_23 | ~spl6_61 | ~spl6_62)),
% 2.02/0.63    inference(forward_demodulation,[],[f661,f483])).
% 2.02/0.63  fof(f483,plain,(
% 2.02/0.63    k1_xboole_0 = k7_relat_1(sK4,sK3) | ~spl6_61),
% 2.02/0.63    inference(avatar_component_clause,[],[f481])).
% 2.02/0.63  fof(f661,plain,(
% 2.02/0.63    k9_relat_1(sK4,k1_xboole_0) = k9_relat_1(k7_relat_1(sK4,sK3),k1_xboole_0) | (~spl6_23 | ~spl6_62)),
% 2.02/0.63    inference(resolution,[],[f321,f494])).
% 2.02/0.63  fof(f494,plain,(
% 2.02/0.63    r1_tarski(k1_xboole_0,sK3) | ~spl6_62),
% 2.02/0.63    inference(avatar_component_clause,[],[f492])).
% 2.02/0.63  fof(f321,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k9_relat_1(sK4,X0) = k9_relat_1(k7_relat_1(sK4,X1),X0)) ) | ~spl6_23),
% 2.02/0.63    inference(resolution,[],[f70,f216])).
% 2.02/0.63  fof(f639,plain,(
% 2.02/0.63    ~spl6_6 | ~spl6_12 | spl6_7 | ~spl6_13 | spl6_2 | spl6_83 | ~spl6_11 | ~spl6_59),
% 2.02/0.63    inference(avatar_split_clause,[],[f631,f470,f152,f637,f107,f162,f132,f157,f127])).
% 2.02/0.63  fof(f470,plain,(
% 2.02/0.63    spl6_59 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 2.02/0.63  fof(f631,plain,(
% 2.02/0.63    ( ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl6_11 | ~spl6_59)),
% 2.02/0.63    inference(resolution,[],[f471,f154])).
% 2.02/0.63  fof(f154,plain,(
% 2.02/0.63    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl6_11),
% 2.02/0.63    inference(avatar_component_clause,[],[f152])).
% 2.02/0.63  fof(f471,plain,(
% 2.02/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl6_59),
% 2.02/0.63    inference(avatar_component_clause,[],[f470])).
% 2.02/0.63  fof(f611,plain,(
% 2.02/0.63    ~spl6_6 | ~spl6_12 | spl6_7 | ~spl6_13 | spl6_2 | spl6_78 | ~spl6_11 | ~spl6_52),
% 2.02/0.63    inference(avatar_split_clause,[],[f603,f431,f152,f609,f107,f162,f132,f157,f127])).
% 2.02/0.63  fof(f431,plain,(
% 2.02/0.63    spl6_52 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 2.02/0.63  fof(f603,plain,(
% 2.02/0.63    ( ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl6_11 | ~spl6_52)),
% 2.02/0.63    inference(resolution,[],[f432,f154])).
% 2.02/0.63  fof(f432,plain,(
% 2.02/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl6_52),
% 2.02/0.63    inference(avatar_component_clause,[],[f431])).
% 2.02/0.63  fof(f552,plain,(
% 2.02/0.63    ~spl6_6 | ~spl6_12 | spl6_7 | ~spl6_13 | spl6_2 | spl6_69 | ~spl6_11 | ~spl6_48),
% 2.02/0.63    inference(avatar_split_clause,[],[f544,f411,f152,f550,f107,f162,f132,f157,f127])).
% 2.02/0.63  fof(f411,plain,(
% 2.02/0.63    spl6_48 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 2.02/0.63  fof(f544,plain,(
% 2.02/0.63    ( ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl6_11 | ~spl6_48)),
% 2.02/0.63    inference(resolution,[],[f412,f154])).
% 2.02/0.63  fof(f412,plain,(
% 2.02/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl6_48),
% 2.02/0.63    inference(avatar_component_clause,[],[f411])).
% 2.02/0.63  fof(f523,plain,(
% 2.02/0.63    spl6_66 | ~spl6_17 | ~spl6_18 | ~spl6_32),
% 2.02/0.63    inference(avatar_split_clause,[],[f518,f276,f185,f180,f520])).
% 2.02/0.63  fof(f180,plain,(
% 2.02/0.63    spl6_17 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 2.02/0.63  fof(f518,plain,(
% 2.02/0.63    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | (~spl6_17 | ~spl6_18 | ~spl6_32)),
% 2.02/0.63    inference(forward_demodulation,[],[f517,f182])).
% 2.02/0.63  fof(f182,plain,(
% 2.02/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl6_17),
% 2.02/0.63    inference(avatar_component_clause,[],[f180])).
% 2.02/0.63  fof(f517,plain,(
% 2.02/0.63    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) | (~spl6_18 | ~spl6_32)),
% 2.02/0.63    inference(forward_demodulation,[],[f512,f187])).
% 2.02/0.63  fof(f512,plain,(
% 2.02/0.63    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) | ~spl6_32),
% 2.02/0.63    inference(resolution,[],[f277,f68])).
% 2.02/0.63  fof(f68,plain,(
% 2.02/0.63    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f28])).
% 2.02/0.63  fof(f28,plain,(
% 2.02/0.63    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f6])).
% 2.02/0.63  fof(f6,axiom,(
% 2.02/0.63    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 2.02/0.63  fof(f508,plain,(
% 2.02/0.63    ~spl6_32 | spl6_65 | ~spl6_18),
% 2.02/0.63    inference(avatar_split_clause,[],[f284,f185,f506,f276])).
% 2.02/0.63  fof(f284,plain,(
% 2.02/0.63    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl6_18),
% 2.02/0.63    inference(superposition,[],[f69,f187])).
% 2.02/0.63  fof(f69,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f29])).
% 2.02/0.63  fof(f29,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f9])).
% 2.02/0.63  fof(f9,axiom,(
% 2.02/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 2.02/0.63  fof(f496,plain,(
% 2.02/0.63    spl6_32 | ~spl6_23 | ~spl6_61),
% 2.02/0.63    inference(avatar_split_clause,[],[f489,f481,f214,f276])).
% 2.02/0.63  fof(f489,plain,(
% 2.02/0.63    v1_relat_1(k1_xboole_0) | (~spl6_23 | ~spl6_61)),
% 2.02/0.63    inference(superposition,[],[f225,f483])).
% 2.02/0.63  fof(f225,plain,(
% 2.02/0.63    ( ! [X1] : (v1_relat_1(k7_relat_1(sK4,X1))) ) | ~spl6_23),
% 2.02/0.63    inference(resolution,[],[f216,f74])).
% 2.02/0.63  fof(f74,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f34])).
% 2.02/0.63  fof(f34,plain,(
% 2.02/0.63    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f5])).
% 2.02/0.63  fof(f5,axiom,(
% 2.02/0.63    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.02/0.63  fof(f495,plain,(
% 2.02/0.63    spl6_62 | ~spl6_18 | ~spl6_23 | ~spl6_61),
% 2.02/0.63    inference(avatar_split_clause,[],[f490,f481,f214,f185,f492])).
% 2.02/0.63  fof(f490,plain,(
% 2.02/0.63    r1_tarski(k1_xboole_0,sK3) | (~spl6_18 | ~spl6_23 | ~spl6_61)),
% 2.02/0.63    inference(forward_demodulation,[],[f488,f187])).
% 2.02/0.63  fof(f488,plain,(
% 2.02/0.63    r1_tarski(k1_relat_1(k1_xboole_0),sK3) | (~spl6_23 | ~spl6_61)),
% 2.02/0.63    inference(superposition,[],[f224,f483])).
% 2.02/0.63  fof(f224,plain,(
% 2.02/0.63    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0)) ) | ~spl6_23),
% 2.02/0.63    inference(resolution,[],[f216,f75])).
% 2.02/0.63  fof(f484,plain,(
% 2.02/0.63    spl6_61 | ~spl6_29 | ~spl6_45),
% 2.02/0.63    inference(avatar_split_clause,[],[f479,f395,f259,f481])).
% 2.02/0.63  fof(f479,plain,(
% 2.02/0.63    k1_xboole_0 = k7_relat_1(sK4,sK3) | (~spl6_29 | ~spl6_45)),
% 2.02/0.63    inference(resolution,[],[f396,f261])).
% 2.02/0.63  fof(f472,plain,(
% 2.02/0.63    spl6_1 | spl6_4 | spl6_59 | ~spl6_3),
% 2.02/0.63    inference(avatar_split_clause,[],[f465,f112,f470,f117,f102])).
% 2.02/0.63  fof(f465,plain,(
% 2.02/0.63    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0)))) ) | ~spl6_3),
% 2.02/0.63    inference(resolution,[],[f92,f114])).
% 2.02/0.63  fof(f114,plain,(
% 2.02/0.63    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl6_3),
% 2.02/0.63    inference(avatar_component_clause,[],[f112])).
% 2.02/0.63  fof(f92,plain,(
% 2.02/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f48])).
% 2.02/0.63  fof(f48,plain,(
% 2.02/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.02/0.63    inference(flattening,[],[f47])).
% 2.02/0.63  fof(f47,plain,(
% 2.02/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f20])).
% 2.02/0.63  fof(f20,axiom,(
% 2.02/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 2.02/0.63  fof(f464,plain,(
% 2.02/0.63    ~spl6_24 | spl6_58 | ~spl6_43),
% 2.02/0.63    inference(avatar_split_clause,[],[f446,f379,f462,f219])).
% 2.02/0.63  fof(f446,plain,(
% 2.02/0.63    ( ! [X2] : (~r1_xboole_0(X2,sK3) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X2)) ) | ~spl6_43),
% 2.02/0.63    inference(superposition,[],[f69,f381])).
% 2.02/0.63  fof(f456,plain,(
% 2.02/0.63    ~spl6_24 | spl6_56 | ~spl6_43),
% 2.02/0.63    inference(avatar_split_clause,[],[f444,f379,f454,f219])).
% 2.02/0.63  fof(f444,plain,(
% 2.02/0.63    ( ! [X0] : (~r1_xboole_0(sK3,X0) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl6_43),
% 2.02/0.63    inference(superposition,[],[f78,f381])).
% 2.02/0.63  fof(f78,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f37])).
% 2.02/0.63  fof(f37,plain,(
% 2.02/0.63    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.02/0.63    inference(ennf_transformation,[],[f12])).
% 2.02/0.63  fof(f12,axiom,(
% 2.02/0.63    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 2.02/0.63  fof(f433,plain,(
% 2.02/0.63    spl6_1 | spl6_4 | spl6_52 | ~spl6_3),
% 2.02/0.63    inference(avatar_split_clause,[],[f426,f112,f431,f117,f102])).
% 2.02/0.63  fof(f426,plain,(
% 2.02/0.63    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0)) ) | ~spl6_3),
% 2.02/0.63    inference(resolution,[],[f91,f114])).
% 2.02/0.63  fof(f91,plain,(
% 2.02/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f48])).
% 2.02/0.63  fof(f413,plain,(
% 2.02/0.63    spl6_1 | spl6_4 | spl6_48 | ~spl6_3),
% 2.02/0.63    inference(avatar_split_clause,[],[f406,f112,f411,f117,f102])).
% 2.02/0.63  fof(f406,plain,(
% 2.02/0.63    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3))) ) | ~spl6_3),
% 2.02/0.63    inference(resolution,[],[f90,f114])).
% 2.02/0.63  fof(f90,plain,(
% 2.02/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f48])).
% 2.02/0.63  fof(f397,plain,(
% 2.02/0.63    ~spl6_23 | spl6_45 | ~spl6_40),
% 2.02/0.63    inference(avatar_split_clause,[],[f385,f363,f395,f214])).
% 2.02/0.63  fof(f385,plain,(
% 2.02/0.63    ( ! [X0] : (~r1_xboole_0(sK2,X0) | ~v1_relat_1(sK4) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl6_40),
% 2.02/0.63    inference(superposition,[],[f78,f365])).
% 2.02/0.63  fof(f382,plain,(
% 2.02/0.63    ~spl6_24 | spl6_43 | ~spl6_27 | ~spl6_39),
% 2.02/0.63    inference(avatar_split_clause,[],[f377,f357,f239,f379,f219])).
% 2.02/0.63  fof(f239,plain,(
% 2.02/0.63    spl6_27 <=> v4_relat_1(sK5,sK3)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 2.02/0.63  fof(f357,plain,(
% 2.02/0.63    spl6_39 <=> v1_partfun1(sK5,sK3)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 2.02/0.63  fof(f377,plain,(
% 2.02/0.63    ~v4_relat_1(sK5,sK3) | sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5) | ~spl6_39),
% 2.02/0.63    inference(resolution,[],[f359,f83])).
% 2.02/0.63  fof(f83,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f41])).
% 2.02/0.63  fof(f41,plain,(
% 2.02/0.63    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.02/0.63    inference(flattening,[],[f40])).
% 2.02/0.63  fof(f40,plain,(
% 2.02/0.63    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.02/0.63    inference(ennf_transformation,[],[f17])).
% 2.02/0.63  fof(f17,axiom,(
% 2.02/0.63    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 2.02/0.63  fof(f359,plain,(
% 2.02/0.63    v1_partfun1(sK5,sK3) | ~spl6_39),
% 2.02/0.63    inference(avatar_component_clause,[],[f357])).
% 2.02/0.63  fof(f376,plain,(
% 2.02/0.63    spl6_42 | ~spl6_13 | ~spl6_11),
% 2.02/0.63    inference(avatar_split_clause,[],[f368,f152,f162,f374])).
% 2.02/0.63  fof(f368,plain,(
% 2.02/0.63    ( ! [X1] : (~v1_funct_1(sK5) | k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl6_11),
% 2.02/0.63    inference(resolution,[],[f89,f154])).
% 2.02/0.63  fof(f89,plain,(
% 2.02/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f46])).
% 2.02/0.63  fof(f46,plain,(
% 2.02/0.63    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.02/0.63    inference(flattening,[],[f45])).
% 2.02/0.63  fof(f45,plain,(
% 2.02/0.63    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.02/0.63    inference(ennf_transformation,[],[f18])).
% 2.02/0.63  fof(f18,axiom,(
% 2.02/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.02/0.63  fof(f372,plain,(
% 2.02/0.63    spl6_41 | ~spl6_10 | ~spl6_8),
% 2.02/0.63    inference(avatar_split_clause,[],[f367,f137,f147,f370])).
% 2.02/0.63  fof(f367,plain,(
% 2.02/0.63    ( ! [X0] : (~v1_funct_1(sK4) | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl6_8),
% 2.02/0.63    inference(resolution,[],[f89,f139])).
% 2.02/0.63  fof(f366,plain,(
% 2.02/0.63    ~spl6_23 | spl6_40 | ~spl6_26 | ~spl6_38),
% 2.02/0.63    inference(avatar_split_clause,[],[f361,f352,f234,f363,f214])).
% 2.02/0.63  fof(f234,plain,(
% 2.02/0.63    spl6_26 <=> v4_relat_1(sK4,sK2)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 2.02/0.63  fof(f352,plain,(
% 2.02/0.63    spl6_38 <=> v1_partfun1(sK4,sK2)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 2.02/0.63  fof(f361,plain,(
% 2.02/0.63    ~v4_relat_1(sK4,sK2) | sK2 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl6_38),
% 2.02/0.63    inference(resolution,[],[f354,f83])).
% 2.02/0.63  fof(f354,plain,(
% 2.02/0.63    v1_partfun1(sK4,sK2) | ~spl6_38),
% 2.02/0.63    inference(avatar_component_clause,[],[f352])).
% 2.02/0.63  fof(f360,plain,(
% 2.02/0.63    spl6_39 | ~spl6_12 | ~spl6_13 | spl6_2 | ~spl6_11),
% 2.02/0.63    inference(avatar_split_clause,[],[f350,f152,f107,f162,f157,f357])).
% 2.02/0.63  fof(f350,plain,(
% 2.02/0.63    v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3) | ~spl6_11),
% 2.02/0.63    inference(resolution,[],[f73,f154])).
% 2.02/0.63  fof(f73,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f33])).
% 2.02/0.63  fof(f33,plain,(
% 2.02/0.63    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.02/0.63    inference(flattening,[],[f32])).
% 2.02/0.63  fof(f32,plain,(
% 2.02/0.63    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.02/0.63    inference(ennf_transformation,[],[f16])).
% 2.02/0.63  fof(f16,axiom,(
% 2.02/0.63    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 2.02/0.63  fof(f355,plain,(
% 2.02/0.63    spl6_38 | ~spl6_9 | ~spl6_10 | spl6_2 | ~spl6_8),
% 2.02/0.63    inference(avatar_split_clause,[],[f349,f137,f107,f147,f142,f352])).
% 2.02/0.63  fof(f349,plain,(
% 2.02/0.63    v1_xboole_0(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2) | ~spl6_8),
% 2.02/0.63    inference(resolution,[],[f73,f139])).
% 2.02/0.63  fof(f269,plain,(
% 2.02/0.63    spl6_30 | ~spl6_29),
% 2.02/0.63    inference(avatar_split_clause,[],[f264,f259,f266])).
% 2.02/0.63  fof(f264,plain,(
% 2.02/0.63    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl6_29),
% 2.02/0.63    inference(resolution,[],[f261,f93])).
% 2.02/0.63  fof(f93,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.02/0.63    inference(definition_unfolding,[],[f85,f72])).
% 2.02/0.63  fof(f85,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f1])).
% 2.02/0.63  fof(f1,axiom,(
% 2.02/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.02/0.63  fof(f262,plain,(
% 2.02/0.63    spl6_4 | spl6_29 | spl6_7 | ~spl6_5),
% 2.02/0.63    inference(avatar_split_clause,[],[f257,f122,f132,f259,f117])).
% 2.02/0.63  fof(f122,plain,(
% 2.02/0.63    spl6_5 <=> r1_subset_1(sK2,sK3)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.02/0.63  fof(f257,plain,(
% 2.02/0.63    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | ~spl6_5),
% 2.02/0.63    inference(resolution,[],[f81,f124])).
% 2.02/0.63  fof(f124,plain,(
% 2.02/0.63    r1_subset_1(sK2,sK3) | ~spl6_5),
% 2.02/0.63    inference(avatar_component_clause,[],[f122])).
% 2.02/0.63  fof(f81,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f39])).
% 2.02/0.63  fof(f39,plain,(
% 2.02/0.63    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.02/0.63    inference(flattening,[],[f38])).
% 2.02/0.63  fof(f38,plain,(
% 2.02/0.63    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f13])).
% 2.02/0.63  fof(f13,axiom,(
% 2.02/0.63    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 2.02/0.63  fof(f242,plain,(
% 2.02/0.63    spl6_27 | ~spl6_11),
% 2.02/0.63    inference(avatar_split_clause,[],[f232,f152,f239])).
% 2.02/0.63  fof(f232,plain,(
% 2.02/0.63    v4_relat_1(sK5,sK3) | ~spl6_11),
% 2.02/0.63    inference(resolution,[],[f88,f154])).
% 2.02/0.63  fof(f88,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f44])).
% 2.02/0.63  fof(f44,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.63    inference(ennf_transformation,[],[f23])).
% 2.02/0.63  fof(f23,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.02/0.63    inference(pure_predicate_removal,[],[f15])).
% 2.02/0.63  fof(f15,axiom,(
% 2.02/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.02/0.63  fof(f237,plain,(
% 2.02/0.63    spl6_26 | ~spl6_8),
% 2.02/0.63    inference(avatar_split_clause,[],[f231,f137,f234])).
% 2.02/0.63  fof(f231,plain,(
% 2.02/0.63    v4_relat_1(sK4,sK2) | ~spl6_8),
% 2.02/0.63    inference(resolution,[],[f88,f139])).
% 2.02/0.63  fof(f222,plain,(
% 2.02/0.63    spl6_24 | ~spl6_11),
% 2.02/0.63    inference(avatar_split_clause,[],[f212,f152,f219])).
% 2.02/0.63  fof(f212,plain,(
% 2.02/0.63    v1_relat_1(sK5) | ~spl6_11),
% 2.02/0.63    inference(resolution,[],[f87,f154])).
% 2.02/0.63  fof(f87,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f43])).
% 2.02/0.63  fof(f43,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.63    inference(ennf_transformation,[],[f14])).
% 2.02/0.63  fof(f14,axiom,(
% 2.02/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.02/0.63  fof(f217,plain,(
% 2.02/0.63    spl6_23 | ~spl6_8),
% 2.02/0.63    inference(avatar_split_clause,[],[f211,f137,f214])).
% 2.02/0.63  fof(f211,plain,(
% 2.02/0.63    v1_relat_1(sK4) | ~spl6_8),
% 2.02/0.63    inference(resolution,[],[f87,f139])).
% 2.02/0.63  fof(f188,plain,(
% 2.02/0.63    spl6_18),
% 2.02/0.63    inference(avatar_split_clause,[],[f63,f185])).
% 2.02/0.63  fof(f63,plain,(
% 2.02/0.63    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.02/0.63    inference(cnf_transformation,[],[f10])).
% 2.02/0.63  fof(f10,axiom,(
% 2.02/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 2.02/0.63  fof(f183,plain,(
% 2.02/0.63    spl6_17),
% 2.02/0.63    inference(avatar_split_clause,[],[f64,f180])).
% 2.02/0.63  fof(f64,plain,(
% 2.02/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.02/0.63    inference(cnf_transformation,[],[f10])).
% 2.02/0.63  fof(f178,plain,(
% 2.02/0.63    ~spl6_14 | ~spl6_15 | ~spl6_16),
% 2.02/0.63    inference(avatar_split_clause,[],[f49,f175,f171,f167])).
% 2.02/0.63  fof(f49,plain,(
% 2.02/0.63    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 2.02/0.63    inference(cnf_transformation,[],[f25])).
% 2.02/0.63  fof(f25,plain,(
% 2.02/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.02/0.63    inference(flattening,[],[f24])).
% 2.02/0.63  fof(f24,plain,(
% 2.02/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f22])).
% 2.02/0.63  fof(f22,negated_conjecture,(
% 2.02/0.63    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 2.02/0.63    inference(negated_conjecture,[],[f21])).
% 2.02/0.63  fof(f21,conjecture,(
% 2.02/0.63    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).
% 2.02/0.63  fof(f165,plain,(
% 2.02/0.63    spl6_13),
% 2.02/0.63    inference(avatar_split_clause,[],[f50,f162])).
% 2.02/0.63  fof(f50,plain,(
% 2.02/0.63    v1_funct_1(sK5)),
% 2.02/0.63    inference(cnf_transformation,[],[f25])).
% 2.02/0.63  fof(f160,plain,(
% 2.02/0.63    spl6_12),
% 2.02/0.63    inference(avatar_split_clause,[],[f51,f157])).
% 2.02/0.63  fof(f51,plain,(
% 2.02/0.63    v1_funct_2(sK5,sK3,sK1)),
% 2.02/0.63    inference(cnf_transformation,[],[f25])).
% 2.02/0.63  fof(f155,plain,(
% 2.02/0.63    spl6_11),
% 2.02/0.63    inference(avatar_split_clause,[],[f52,f152])).
% 2.02/0.63  fof(f52,plain,(
% 2.02/0.63    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.02/0.63    inference(cnf_transformation,[],[f25])).
% 2.02/0.63  fof(f150,plain,(
% 2.02/0.63    spl6_10),
% 2.02/0.63    inference(avatar_split_clause,[],[f53,f147])).
% 2.02/0.63  fof(f53,plain,(
% 2.02/0.63    v1_funct_1(sK4)),
% 2.02/0.63    inference(cnf_transformation,[],[f25])).
% 2.02/0.63  fof(f145,plain,(
% 2.02/0.63    spl6_9),
% 2.02/0.63    inference(avatar_split_clause,[],[f54,f142])).
% 2.02/0.63  fof(f54,plain,(
% 2.02/0.63    v1_funct_2(sK4,sK2,sK1)),
% 2.02/0.63    inference(cnf_transformation,[],[f25])).
% 2.02/0.63  fof(f140,plain,(
% 2.02/0.63    spl6_8),
% 2.02/0.63    inference(avatar_split_clause,[],[f55,f137])).
% 2.02/0.63  fof(f55,plain,(
% 2.02/0.63    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.02/0.63    inference(cnf_transformation,[],[f25])).
% 2.02/0.63  fof(f135,plain,(
% 2.02/0.63    ~spl6_7),
% 2.02/0.63    inference(avatar_split_clause,[],[f56,f132])).
% 2.02/0.63  fof(f56,plain,(
% 2.02/0.63    ~v1_xboole_0(sK3)),
% 2.02/0.63    inference(cnf_transformation,[],[f25])).
% 2.02/0.63  fof(f130,plain,(
% 2.02/0.63    spl6_6),
% 2.02/0.63    inference(avatar_split_clause,[],[f57,f127])).
% 2.02/0.63  fof(f57,plain,(
% 2.02/0.63    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.02/0.63    inference(cnf_transformation,[],[f25])).
% 2.02/0.63  fof(f125,plain,(
% 2.02/0.63    spl6_5),
% 2.02/0.63    inference(avatar_split_clause,[],[f58,f122])).
% 2.02/0.63  fof(f58,plain,(
% 2.02/0.63    r1_subset_1(sK2,sK3)),
% 2.02/0.63    inference(cnf_transformation,[],[f25])).
% 2.02/0.63  fof(f120,plain,(
% 2.02/0.63    ~spl6_4),
% 2.02/0.63    inference(avatar_split_clause,[],[f59,f117])).
% 2.02/0.63  fof(f59,plain,(
% 2.02/0.63    ~v1_xboole_0(sK2)),
% 2.02/0.63    inference(cnf_transformation,[],[f25])).
% 2.02/0.63  fof(f115,plain,(
% 2.02/0.63    spl6_3),
% 2.02/0.63    inference(avatar_split_clause,[],[f60,f112])).
% 2.02/0.63  fof(f60,plain,(
% 2.02/0.63    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.02/0.63    inference(cnf_transformation,[],[f25])).
% 2.02/0.63  fof(f110,plain,(
% 2.02/0.63    ~spl6_2),
% 2.02/0.63    inference(avatar_split_clause,[],[f61,f107])).
% 2.02/0.63  fof(f61,plain,(
% 2.02/0.63    ~v1_xboole_0(sK1)),
% 2.02/0.63    inference(cnf_transformation,[],[f25])).
% 2.02/0.63  fof(f105,plain,(
% 2.02/0.63    ~spl6_1),
% 2.02/0.63    inference(avatar_split_clause,[],[f62,f102])).
% 2.02/0.63  fof(f62,plain,(
% 2.02/0.63    ~v1_xboole_0(sK0)),
% 2.02/0.63    inference(cnf_transformation,[],[f25])).
% 2.02/0.63  % SZS output end Proof for theBenchmark
% 2.02/0.63  % (13941)------------------------------
% 2.02/0.63  % (13941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.63  % (13941)Termination reason: Refutation
% 2.02/0.63  
% 2.02/0.63  % (13941)Memory used [KB]: 12025
% 2.02/0.63  % (13941)Time elapsed: 0.209 s
% 2.02/0.63  % (13941)------------------------------
% 2.02/0.63  % (13941)------------------------------
% 2.02/0.63  % (13924)Success in time 0.267 s
%------------------------------------------------------------------------------
