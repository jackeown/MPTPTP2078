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
% DateTime   : Thu Dec  3 13:17:25 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  318 ( 707 expanded)
%              Number of leaves         :   76 ( 346 expanded)
%              Depth                    :   14
%              Number of atoms          : 1523 (3270 expanded)
%              Number of equality atoms :  176 ( 472 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1245,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f112,f117,f122,f127,f132,f137,f142,f147,f152,f157,f162,f167,f180,f185,f190,f195,f201,f231,f236,f248,f265,f270,f276,f283,f367,f372,f378,f384,f390,f394,f408,f424,f446,f464,f472,f480,f490,f497,f509,f516,f526,f559,f590,f649,f678,f687,f715,f738,f748,f764,f844,f880,f1158,f1166,f1244])).

fof(f1244,plain,
    ( ~ spl6_99
    | ~ spl6_6
    | spl6_16
    | ~ spl6_33
    | ~ spl6_47
    | ~ spl6_48
    | ~ spl6_104 ),
    inference(avatar_split_clause,[],[f1243,f745,f392,f388,f280,f177,f129,f712])).

fof(f712,plain,
    ( spl6_99
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).

fof(f129,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f177,plain,
    ( spl6_16
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f280,plain,
    ( spl6_33
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f388,plain,
    ( spl6_47
  <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f392,plain,
    ( spl6_48
  <=> ! [X1] : k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f745,plain,
    ( spl6_104
  <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).

fof(f1243,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_6
    | spl6_16
    | ~ spl6_33
    | ~ spl6_47
    | ~ spl6_48
    | ~ spl6_104 ),
    inference(forward_demodulation,[],[f1242,f747])).

fof(f747,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_104 ),
    inference(avatar_component_clause,[],[f745])).

fof(f1242,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_6
    | spl6_16
    | ~ spl6_33
    | ~ spl6_47
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f1241,f389])).

fof(f389,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f388])).

fof(f1241,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl6_6
    | spl6_16
    | ~ spl6_33
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f1240,f282])).

fof(f282,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f280])).

fof(f1240,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl6_6
    | spl6_16
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f1239,f351])).

fof(f351,plain,
    ( ! [X1] : k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))
    | ~ spl6_6 ),
    inference(resolution,[],[f97,f131])).

fof(f131,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f88,f75])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f1239,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_16
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f179,f393])).

fof(f393,plain,
    ( ! [X1] : k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1)
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f392])).

fof(f179,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f177])).

fof(f1166,plain,
    ( spl6_14
    | spl6_1
    | ~ spl6_117
    | ~ spl6_107
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
    | ~ spl6_33
    | ~ spl6_47
    | ~ spl6_48
    | ~ spl6_99
    | ~ spl6_104
    | ~ spl6_121 ),
    inference(avatar_split_clause,[],[f1165,f877,f745,f712,f392,f388,f280,f129,f109,f119,f114,f134,f129,f149,f144,f139,f164,f159,f154,f761,f841,f104,f169])).

fof(f169,plain,
    ( spl6_14
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f104,plain,
    ( spl6_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f841,plain,
    ( spl6_117
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_117])])).

fof(f761,plain,
    ( spl6_107
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).

fof(f154,plain,
    ( spl6_11
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f159,plain,
    ( spl6_12
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f164,plain,
    ( spl6_13
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f139,plain,
    ( spl6_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f144,plain,
    ( spl6_9
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f149,plain,
    ( spl6_10
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f134,plain,
    ( spl6_7
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f114,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f119,plain,
    ( spl6_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f109,plain,
    ( spl6_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f877,plain,
    ( spl6_121
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_121])])).

fof(f1165,plain,
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
    | ~ spl6_33
    | ~ spl6_47
    | ~ spl6_48
    | ~ spl6_99
    | ~ spl6_104
    | ~ spl6_121 ),
    inference(trivial_inequality_removal,[],[f1164])).

fof(f1164,plain,
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
    | ~ spl6_33
    | ~ spl6_47
    | ~ spl6_48
    | ~ spl6_99
    | ~ spl6_104
    | ~ spl6_121 ),
    inference(forward_demodulation,[],[f1163,f714])).

fof(f714,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_99 ),
    inference(avatar_component_clause,[],[f712])).

fof(f1163,plain,
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
    | ~ spl6_33
    | ~ spl6_47
    | ~ spl6_48
    | ~ spl6_104
    | ~ spl6_121 ),
    inference(forward_demodulation,[],[f1162,f747])).

fof(f1162,plain,
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
    | ~ spl6_33
    | ~ spl6_47
    | ~ spl6_48
    | ~ spl6_121 ),
    inference(forward_demodulation,[],[f1161,f389])).

fof(f1161,plain,
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
    | ~ spl6_33
    | ~ spl6_48
    | ~ spl6_121 ),
    inference(forward_demodulation,[],[f1160,f282])).

fof(f1160,plain,
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
    | ~ spl6_48
    | ~ spl6_121 ),
    inference(forward_demodulation,[],[f1159,f351])).

fof(f1159,plain,
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
    | ~ spl6_48
    | ~ spl6_121 ),
    inference(forward_demodulation,[],[f1135,f393])).

fof(f1135,plain,
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
    | ~ spl6_121 ),
    inference(resolution,[],[f879,f100])).

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

fof(f879,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_121 ),
    inference(avatar_component_clause,[],[f877])).

fof(f1158,plain,
    ( spl6_15
    | spl6_1
    | ~ spl6_117
    | ~ spl6_107
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
    | ~ spl6_33
    | ~ spl6_47
    | ~ spl6_48
    | ~ spl6_99
    | ~ spl6_104
    | ~ spl6_121 ),
    inference(avatar_split_clause,[],[f1157,f877,f745,f712,f392,f388,f280,f129,f109,f119,f114,f134,f129,f149,f144,f139,f164,f159,f154,f761,f841,f104,f173])).

fof(f173,plain,
    ( spl6_15
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f1157,plain,
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
    | ~ spl6_33
    | ~ spl6_47
    | ~ spl6_48
    | ~ spl6_99
    | ~ spl6_104
    | ~ spl6_121 ),
    inference(trivial_inequality_removal,[],[f1156])).

fof(f1156,plain,
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
    | ~ spl6_33
    | ~ spl6_47
    | ~ spl6_48
    | ~ spl6_99
    | ~ spl6_104
    | ~ spl6_121 ),
    inference(forward_demodulation,[],[f1155,f714])).

fof(f1155,plain,
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
    | ~ spl6_33
    | ~ spl6_47
    | ~ spl6_48
    | ~ spl6_104
    | ~ spl6_121 ),
    inference(forward_demodulation,[],[f1154,f747])).

fof(f1154,plain,
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
    | ~ spl6_33
    | ~ spl6_47
    | ~ spl6_48
    | ~ spl6_121 ),
    inference(forward_demodulation,[],[f1153,f389])).

fof(f1153,plain,
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
    | ~ spl6_33
    | ~ spl6_48
    | ~ spl6_121 ),
    inference(forward_demodulation,[],[f1152,f282])).

fof(f1152,plain,
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
    | ~ spl6_48
    | ~ spl6_121 ),
    inference(forward_demodulation,[],[f1151,f351])).

fof(f1151,plain,
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
    | ~ spl6_48
    | ~ spl6_121 ),
    inference(forward_demodulation,[],[f1134,f393])).

fof(f1134,plain,
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
    | ~ spl6_121 ),
    inference(resolution,[],[f879,f101])).

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
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
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

fof(f880,plain,
    ( spl6_121
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_83 ),
    inference(avatar_split_clause,[],[f875,f588,f139,f144,f149,f877])).

fof(f588,plain,
    ( spl6_83
  <=> ! [X1] :
        ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f875,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_8
    | ~ spl6_83 ),
    inference(resolution,[],[f589,f141])).

fof(f141,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f589,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) )
    | ~ spl6_83 ),
    inference(avatar_component_clause,[],[f588])).

fof(f844,plain,
    ( spl6_117
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_77 ),
    inference(avatar_split_clause,[],[f839,f557,f139,f144,f149,f841])).

fof(f557,plain,
    ( spl6_77
  <=> ! [X1] :
        ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f839,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_8
    | ~ spl6_77 ),
    inference(resolution,[],[f558,f141])).

fof(f558,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) )
    | ~ spl6_77 ),
    inference(avatar_component_clause,[],[f557])).

fof(f764,plain,
    ( spl6_107
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_71 ),
    inference(avatar_split_clause,[],[f759,f524,f139,f144,f149,f761])).

fof(f524,plain,
    ( spl6_71
  <=> ! [X1] :
        ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f759,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_8
    | ~ spl6_71 ),
    inference(resolution,[],[f525,f141])).

fof(f525,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) )
    | ~ spl6_71 ),
    inference(avatar_component_clause,[],[f524])).

fof(f748,plain,
    ( spl6_104
    | ~ spl6_60
    | ~ spl6_103 ),
    inference(avatar_split_clause,[],[f740,f735,f462,f745])).

fof(f462,plain,
    ( spl6_60
  <=> ! [X0] :
        ( ~ r1_xboole_0(sK3,X0)
        | k1_xboole_0 = k7_relat_1(sK5,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f735,plain,
    ( spl6_103
  <=> r1_xboole_0(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).

fof(f740,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_60
    | ~ spl6_103 ),
    inference(resolution,[],[f737,f463])).

fof(f463,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK3,X0)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f462])).

fof(f737,plain,
    ( r1_xboole_0(sK3,k1_xboole_0)
    | ~ spl6_103 ),
    inference(avatar_component_clause,[],[f735])).

fof(f738,plain,
    ( spl6_103
    | ~ spl6_26
    | ~ spl6_46
    | ~ spl6_95 ),
    inference(avatar_split_clause,[],[f733,f675,f381,f233,f735])).

fof(f233,plain,
    ( spl6_26
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f381,plain,
    ( spl6_46
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f675,plain,
    ( spl6_95
  <=> k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).

fof(f733,plain,
    ( r1_xboole_0(sK3,k1_xboole_0)
    | ~ spl6_26
    | ~ spl6_46
    | ~ spl6_95 ),
    inference(trivial_inequality_removal,[],[f732])).

fof(f732,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK3,k1_xboole_0)
    | ~ spl6_26
    | ~ spl6_46
    | ~ spl6_95 ),
    inference(superposition,[],[f560,f677])).

fof(f677,plain,
    ( k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0)
    | ~ spl6_95 ),
    inference(avatar_component_clause,[],[f675])).

fof(f560,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k9_relat_1(sK5,X2)
        | r1_xboole_0(sK3,X2) )
    | ~ spl6_26
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f308,f383])).

fof(f383,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f381])).

fof(f308,plain,
    ( ! [X2] :
        ( r1_xboole_0(k1_relat_1(sK5),X2)
        | k1_xboole_0 != k9_relat_1(sK5,X2) )
    | ~ spl6_26 ),
    inference(resolution,[],[f79,f235])).

fof(f235,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f233])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f715,plain,
    ( spl6_99
    | ~ spl6_50
    | ~ spl6_96 ),
    inference(avatar_split_clause,[],[f707,f684,f406,f712])).

fof(f406,plain,
    ( spl6_50
  <=> ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | k1_xboole_0 = k7_relat_1(sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f684,plain,
    ( spl6_96
  <=> r1_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).

fof(f707,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_50
    | ~ spl6_96 ),
    inference(resolution,[],[f686,f407])).

fof(f407,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f406])).

fof(f686,plain,
    ( r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl6_96 ),
    inference(avatar_component_clause,[],[f684])).

fof(f687,plain,
    ( spl6_96
    | ~ spl6_25
    | ~ spl6_45
    | ~ spl6_91 ),
    inference(avatar_split_clause,[],[f682,f646,f375,f228,f684])).

fof(f228,plain,
    ( spl6_25
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f375,plain,
    ( spl6_45
  <=> sK2 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f646,plain,
    ( spl6_91
  <=> k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f682,plain,
    ( r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl6_25
    | ~ spl6_45
    | ~ spl6_91 ),
    inference(trivial_inequality_removal,[],[f681])).

fof(f681,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl6_25
    | ~ spl6_45
    | ~ spl6_91 ),
    inference(superposition,[],[f527,f648])).

fof(f648,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0)
    | ~ spl6_91 ),
    inference(avatar_component_clause,[],[f646])).

fof(f527,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k9_relat_1(sK4,X1)
        | r1_xboole_0(sK2,X1) )
    | ~ spl6_25
    | ~ spl6_45 ),
    inference(forward_demodulation,[],[f307,f377])).

fof(f377,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f375])).

fof(f307,plain,
    ( ! [X1] :
        ( r1_xboole_0(k1_relat_1(sK4),X1)
        | k1_xboole_0 != k9_relat_1(sK4,X1) )
    | ~ spl6_25 ),
    inference(resolution,[],[f79,f230])).

fof(f230,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f228])).

fof(f678,plain,
    ( spl6_95
    | ~ spl6_26
    | ~ spl6_27
    | ~ spl6_68
    | ~ spl6_69 ),
    inference(avatar_split_clause,[],[f673,f513,f506,f245,f233,f675])).

fof(f245,plain,
    ( spl6_27
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f506,plain,
    ( spl6_68
  <=> k1_xboole_0 = k7_relat_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f513,plain,
    ( spl6_69
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f673,plain,
    ( k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0)
    | ~ spl6_26
    | ~ spl6_27
    | ~ spl6_68
    | ~ spl6_69 ),
    inference(forward_demodulation,[],[f672,f247])).

fof(f247,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f245])).

fof(f672,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0)
    | ~ spl6_26
    | ~ spl6_68
    | ~ spl6_69 ),
    inference(forward_demodulation,[],[f661,f508])).

fof(f508,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f506])).

fof(f661,plain,
    ( k9_relat_1(sK5,k1_xboole_0) = k9_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0)
    | ~ spl6_26
    | ~ spl6_69 ),
    inference(resolution,[],[f358,f515])).

fof(f515,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl6_69 ),
    inference(avatar_component_clause,[],[f513])).

fof(f358,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(X4,X5)
        | k9_relat_1(k7_relat_1(sK5,X5),X4) = k9_relat_1(sK5,X4) )
    | ~ spl6_26 ),
    inference(resolution,[],[f72,f235])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f649,plain,
    ( spl6_91
    | ~ spl6_25
    | ~ spl6_27
    | ~ spl6_65
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f644,f494,f487,f245,f228,f646])).

fof(f487,plain,
    ( spl6_65
  <=> k1_xboole_0 = k7_relat_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f494,plain,
    ( spl6_66
  <=> r1_tarski(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f644,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0)
    | ~ spl6_25
    | ~ spl6_27
    | ~ spl6_65
    | ~ spl6_66 ),
    inference(forward_demodulation,[],[f643,f247])).

fof(f643,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0)
    | ~ spl6_25
    | ~ spl6_65
    | ~ spl6_66 ),
    inference(forward_demodulation,[],[f636,f489])).

fof(f489,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl6_65 ),
    inference(avatar_component_clause,[],[f487])).

fof(f636,plain,
    ( k9_relat_1(sK4,k1_xboole_0) = k9_relat_1(k7_relat_1(sK4,sK3),k1_xboole_0)
    | ~ spl6_25
    | ~ spl6_66 ),
    inference(resolution,[],[f357,f496])).

fof(f496,plain,
    ( r1_tarski(k1_xboole_0,sK3)
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f494])).

fof(f357,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k9_relat_1(k7_relat_1(sK4,X3),X2) = k9_relat_1(sK4,X2) )
    | ~ spl6_25 ),
    inference(resolution,[],[f72,f230])).

fof(f590,plain,
    ( ~ spl6_6
    | ~ spl6_12
    | spl6_7
    | ~ spl6_13
    | spl6_2
    | spl6_83
    | ~ spl6_11
    | ~ spl6_63 ),
    inference(avatar_split_clause,[],[f582,f478,f154,f588,f109,f164,f134,f159,f129])).

fof(f478,plain,
    ( spl6_63
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f582,plain,
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
    | ~ spl6_63 ),
    inference(resolution,[],[f479,f156])).

fof(f156,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f479,plain,
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
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f478])).

fof(f559,plain,
    ( ~ spl6_6
    | ~ spl6_12
    | spl6_7
    | ~ spl6_13
    | spl6_2
    | spl6_77
    | ~ spl6_11
    | ~ spl6_57 ),
    inference(avatar_split_clause,[],[f551,f444,f154,f557,f109,f164,f134,f159,f129])).

fof(f444,plain,
    ( spl6_57
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f551,plain,
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
    | ~ spl6_57 ),
    inference(resolution,[],[f445,f156])).

fof(f445,plain,
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
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f444])).

fof(f526,plain,
    ( ~ spl6_6
    | ~ spl6_12
    | spl6_7
    | ~ spl6_13
    | spl6_2
    | spl6_71
    | ~ spl6_11
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f518,f422,f154,f524,f109,f164,f134,f159,f129])).

fof(f422,plain,
    ( spl6_53
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f518,plain,
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
    | ~ spl6_53 ),
    inference(resolution,[],[f423,f156])).

fof(f423,plain,
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
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f422])).

fof(f516,plain,
    ( spl6_69
    | ~ spl6_19
    | ~ spl6_26
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f511,f506,f233,f192,f513])).

fof(f192,plain,
    ( spl6_19
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f511,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl6_19
    | ~ spl6_26
    | ~ spl6_68 ),
    inference(forward_demodulation,[],[f510,f194])).

fof(f194,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f192])).

fof(f510,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK2)
    | ~ spl6_26
    | ~ spl6_68 ),
    inference(superposition,[],[f238,f508])).

fof(f238,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),X0)
    | ~ spl6_26 ),
    inference(resolution,[],[f235,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f509,plain,
    ( spl6_68
    | ~ spl6_32
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f504,f470,f273,f506])).

fof(f273,plain,
    ( spl6_32
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f470,plain,
    ( spl6_62
  <=> ! [X2] :
        ( ~ r1_xboole_0(X2,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f504,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl6_32
    | ~ spl6_62 ),
    inference(resolution,[],[f471,f275])).

fof(f275,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f273])).

fof(f471,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X2) )
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f470])).

fof(f497,plain,
    ( spl6_66
    | ~ spl6_19
    | ~ spl6_25
    | ~ spl6_65 ),
    inference(avatar_split_clause,[],[f492,f487,f228,f192,f494])).

fof(f492,plain,
    ( r1_tarski(k1_xboole_0,sK3)
    | ~ spl6_19
    | ~ spl6_25
    | ~ spl6_65 ),
    inference(forward_demodulation,[],[f491,f194])).

fof(f491,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK3)
    | ~ spl6_25
    | ~ spl6_65 ),
    inference(superposition,[],[f237,f489])).

fof(f237,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0)
    | ~ spl6_25 ),
    inference(resolution,[],[f230,f77])).

fof(f490,plain,
    ( spl6_65
    | ~ spl6_32
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f485,f406,f273,f487])).

fof(f485,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl6_32
    | ~ spl6_50 ),
    inference(resolution,[],[f407,f275])).

fof(f480,plain,
    ( spl6_1
    | spl6_4
    | spl6_63
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f473,f114,f478,f119,f104])).

fof(f473,plain,
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
    inference(resolution,[],[f94,f116])).

fof(f116,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl6_3 ),
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
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

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

fof(f472,plain,
    ( ~ spl6_26
    | spl6_62
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f454,f381,f470,f233])).

fof(f454,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK3)
        | ~ v1_relat_1(sK5)
        | k1_xboole_0 = k7_relat_1(sK5,X2) )
    | ~ spl6_46 ),
    inference(superposition,[],[f71,f383])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f464,plain,
    ( ~ spl6_26
    | spl6_60
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f452,f381,f462,f233])).

fof(f452,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK3,X0)
        | ~ v1_relat_1(sK5)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl6_46 ),
    inference(superposition,[],[f80,f383])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f446,plain,
    ( spl6_1
    | spl6_4
    | spl6_57
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f439,f114,f444,f119,f104])).

fof(f439,plain,
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
    inference(cnf_transformation,[],[f49])).

fof(f424,plain,
    ( spl6_1
    | spl6_4
    | spl6_53
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f417,f114,f422,f119,f104])).

fof(f417,plain,
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
    inference(cnf_transformation,[],[f49])).

fof(f408,plain,
    ( ~ spl6_25
    | spl6_50
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f396,f375,f406,f228])).

fof(f396,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | ~ v1_relat_1(sK4)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl6_45 ),
    inference(superposition,[],[f80,f377])).

fof(f394,plain,
    ( spl6_48
    | ~ spl6_13
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f386,f154,f164,f392])).

fof(f386,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK5)
        | k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1) )
    | ~ spl6_11 ),
    inference(resolution,[],[f91,f156])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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

fof(f390,plain,
    ( spl6_47
    | ~ spl6_10
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f385,f139,f149,f388])).

fof(f385,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) )
    | ~ spl6_8 ),
    inference(resolution,[],[f91,f141])).

fof(f384,plain,
    ( ~ spl6_26
    | spl6_46
    | ~ spl6_31
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f379,f369,f267,f381,f233])).

fof(f267,plain,
    ( spl6_31
  <=> v4_relat_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f369,plain,
    ( spl6_44
  <=> v1_partfun1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f379,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl6_44 ),
    inference(resolution,[],[f371,f85])).

fof(f85,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f371,plain,
    ( v1_partfun1(sK5,sK3)
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f369])).

fof(f378,plain,
    ( ~ spl6_25
    | spl6_45
    | ~ spl6_30
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f373,f364,f262,f375,f228])).

fof(f262,plain,
    ( spl6_30
  <=> v4_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f364,plain,
    ( spl6_43
  <=> v1_partfun1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f373,plain,
    ( ~ v4_relat_1(sK4,sK2)
    | sK2 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl6_43 ),
    inference(resolution,[],[f366,f85])).

fof(f366,plain,
    ( v1_partfun1(sK4,sK2)
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f364])).

fof(f372,plain,
    ( spl6_44
    | ~ spl6_12
    | ~ spl6_13
    | spl6_2
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f362,f154,f109,f164,f159,f369])).

fof(f362,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f76,f156])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f367,plain,
    ( spl6_43
    | ~ spl6_9
    | ~ spl6_10
    | spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f361,f139,f109,f149,f144,f364])).

fof(f361,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f76,f141])).

fof(f283,plain,
    ( spl6_33
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f278,f273,f280])).

fof(f278,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl6_32 ),
    inference(resolution,[],[f275,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f87,f75])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f276,plain,
    ( spl6_4
    | spl6_32
    | spl6_7
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f271,f124,f134,f273,f119])).

fof(f124,plain,
    ( spl6_5
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f271,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f83,f126])).

fof(f126,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f83,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f270,plain,
    ( spl6_31
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f260,f154,f267])).

fof(f260,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f90,f156])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f265,plain,
    ( spl6_30
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f259,f139,f262])).

fof(f259,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f90,f141])).

fof(f248,plain,
    ( spl6_27
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f243,f198,f192,f187,f245])).

fof(f187,plain,
    ( spl6_18
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f198,plain,
    ( spl6_20
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f243,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f242,f189])).

fof(f189,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f187])).

fof(f242,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_19
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f239,f194])).

fof(f239,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl6_20 ),
    inference(resolution,[],[f70,f200])).

fof(f200,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f198])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f236,plain,
    ( spl6_26
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f226,f154,f233])).

fof(f226,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_11 ),
    inference(resolution,[],[f89,f156])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f231,plain,
    ( spl6_25
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f225,f139,f228])).

fof(f225,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_8 ),
    inference(resolution,[],[f89,f141])).

fof(f201,plain,
    ( spl6_20
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f196,f182,f198])).

fof(f182,plain,
    ( spl6_17
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f196,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_17 ),
    inference(resolution,[],[f73,f184])).

fof(f184,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f182])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f195,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f65,f192])).

fof(f65,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f190,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f66,f187])).

fof(f66,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f185,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f64,f182])).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f180,plain,
    ( ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f50,f177,f173,f169])).

fof(f50,plain,
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

fof(f167,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f51,f164])).

fof(f51,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f162,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f52,f159])).

fof(f52,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f157,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f53,f154])).

fof(f53,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f152,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f54,f149])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f147,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f55,f144])).

fof(f55,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f142,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f56,f139])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f137,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f57,f134])).

fof(f57,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f132,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f58,f129])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f127,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f59,f124])).

fof(f59,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f122,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f60,f119])).

fof(f60,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f117,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f61,f114])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f112,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f62,f109])).

fof(f62,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f107,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f63,f104])).

fof(f63,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:27:50 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.53  % (9184)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (9176)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (9192)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (9165)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (9164)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (9167)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (9168)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (9177)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (9166)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (9187)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (9181)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (9179)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (9172)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (9169)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (9189)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (9182)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (9183)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (9178)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (9171)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (9188)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (9185)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (9173)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (9175)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (9174)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.57  % (9180)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.57  % (9190)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.57  % (9193)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.57  % (9191)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.57  % (9181)Refutation not found, incomplete strategy% (9181)------------------------------
% 0.22/0.57  % (9181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (9181)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (9181)Memory used [KB]: 10746
% 0.22/0.57  % (9181)Time elapsed: 0.147 s
% 0.22/0.57  % (9181)------------------------------
% 0.22/0.57  % (9181)------------------------------
% 0.22/0.59  % (9170)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.59  % (9186)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.79/0.62  % (9180)Refutation found. Thanks to Tanya!
% 1.79/0.62  % SZS status Theorem for theBenchmark
% 1.79/0.62  % SZS output start Proof for theBenchmark
% 1.79/0.62  fof(f1245,plain,(
% 1.79/0.62    $false),
% 1.79/0.62    inference(avatar_sat_refutation,[],[f107,f112,f117,f122,f127,f132,f137,f142,f147,f152,f157,f162,f167,f180,f185,f190,f195,f201,f231,f236,f248,f265,f270,f276,f283,f367,f372,f378,f384,f390,f394,f408,f424,f446,f464,f472,f480,f490,f497,f509,f516,f526,f559,f590,f649,f678,f687,f715,f738,f748,f764,f844,f880,f1158,f1166,f1244])).
% 1.79/0.62  fof(f1244,plain,(
% 1.79/0.62    ~spl6_99 | ~spl6_6 | spl6_16 | ~spl6_33 | ~spl6_47 | ~spl6_48 | ~spl6_104),
% 1.79/0.62    inference(avatar_split_clause,[],[f1243,f745,f392,f388,f280,f177,f129,f712])).
% 1.79/0.62  fof(f712,plain,(
% 1.79/0.62    spl6_99 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).
% 1.79/0.62  fof(f129,plain,(
% 1.79/0.62    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.79/0.62  fof(f177,plain,(
% 1.79/0.62    spl6_16 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.79/0.62  fof(f280,plain,(
% 1.79/0.62    spl6_33 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 1.79/0.62  fof(f388,plain,(
% 1.79/0.62    spl6_47 <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 1.79/0.62  fof(f392,plain,(
% 1.79/0.62    spl6_48 <=> ! [X1] : k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 1.79/0.62  fof(f745,plain,(
% 1.79/0.62    spl6_104 <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).
% 1.79/0.62  fof(f1243,plain,(
% 1.79/0.62    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | (~spl6_6 | spl6_16 | ~spl6_33 | ~spl6_47 | ~spl6_48 | ~spl6_104)),
% 1.79/0.62    inference(forward_demodulation,[],[f1242,f747])).
% 1.79/0.62  fof(f747,plain,(
% 1.79/0.62    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | ~spl6_104),
% 1.79/0.62    inference(avatar_component_clause,[],[f745])).
% 1.79/0.62  fof(f1242,plain,(
% 1.79/0.62    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | (~spl6_6 | spl6_16 | ~spl6_33 | ~spl6_47 | ~spl6_48)),
% 1.79/0.62    inference(forward_demodulation,[],[f1241,f389])).
% 1.79/0.62  fof(f389,plain,(
% 1.79/0.62    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl6_47),
% 1.79/0.62    inference(avatar_component_clause,[],[f388])).
% 1.79/0.62  fof(f1241,plain,(
% 1.79/0.62    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (~spl6_6 | spl6_16 | ~spl6_33 | ~spl6_48)),
% 1.79/0.62    inference(forward_demodulation,[],[f1240,f282])).
% 1.79/0.62  fof(f282,plain,(
% 1.79/0.62    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl6_33),
% 1.79/0.62    inference(avatar_component_clause,[],[f280])).
% 1.79/0.62  fof(f1240,plain,(
% 1.79/0.62    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | (~spl6_6 | spl6_16 | ~spl6_48)),
% 1.79/0.62    inference(forward_demodulation,[],[f1239,f351])).
% 1.79/0.62  fof(f351,plain,(
% 1.79/0.62    ( ! [X1] : (k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))) ) | ~spl6_6),
% 1.79/0.62    inference(resolution,[],[f97,f131])).
% 1.79/0.62  fof(f131,plain,(
% 1.79/0.62    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl6_6),
% 1.79/0.62    inference(avatar_component_clause,[],[f129])).
% 1.79/0.62  fof(f97,plain,(
% 1.79/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 1.79/0.62    inference(definition_unfolding,[],[f88,f75])).
% 1.79/0.62  fof(f75,plain,(
% 1.79/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.79/0.62    inference(cnf_transformation,[],[f5])).
% 1.79/0.62  fof(f5,axiom,(
% 1.79/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.79/0.62  fof(f88,plain,(
% 1.79/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f43])).
% 1.79/0.62  fof(f43,plain,(
% 1.79/0.62    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f3])).
% 1.79/0.62  fof(f3,axiom,(
% 1.79/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.79/0.62  fof(f1239,plain,(
% 1.79/0.62    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (spl6_16 | ~spl6_48)),
% 1.79/0.62    inference(forward_demodulation,[],[f179,f393])).
% 1.79/0.62  fof(f393,plain,(
% 1.79/0.62    ( ! [X1] : (k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1)) ) | ~spl6_48),
% 1.79/0.62    inference(avatar_component_clause,[],[f392])).
% 1.79/0.62  fof(f179,plain,(
% 1.79/0.62    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_16),
% 1.79/0.62    inference(avatar_component_clause,[],[f177])).
% 1.79/0.62  fof(f1166,plain,(
% 1.79/0.62    spl6_14 | spl6_1 | ~spl6_117 | ~spl6_107 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_6 | spl6_7 | ~spl6_3 | spl6_4 | spl6_2 | ~spl6_6 | ~spl6_33 | ~spl6_47 | ~spl6_48 | ~spl6_99 | ~spl6_104 | ~spl6_121),
% 1.79/0.62    inference(avatar_split_clause,[],[f1165,f877,f745,f712,f392,f388,f280,f129,f109,f119,f114,f134,f129,f149,f144,f139,f164,f159,f154,f761,f841,f104,f169])).
% 1.79/0.62  fof(f169,plain,(
% 1.79/0.62    spl6_14 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.79/0.62  fof(f104,plain,(
% 1.79/0.62    spl6_1 <=> v1_xboole_0(sK0)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.79/0.62  fof(f841,plain,(
% 1.79/0.62    spl6_117 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_117])])).
% 1.79/0.62  fof(f761,plain,(
% 1.79/0.62    spl6_107 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).
% 1.79/0.62  fof(f154,plain,(
% 1.79/0.62    spl6_11 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.79/0.62  fof(f159,plain,(
% 1.79/0.62    spl6_12 <=> v1_funct_2(sK5,sK3,sK1)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.79/0.62  fof(f164,plain,(
% 1.79/0.62    spl6_13 <=> v1_funct_1(sK5)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.79/0.62  fof(f139,plain,(
% 1.79/0.62    spl6_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.79/0.62  fof(f144,plain,(
% 1.79/0.62    spl6_9 <=> v1_funct_2(sK4,sK2,sK1)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.79/0.62  fof(f149,plain,(
% 1.79/0.62    spl6_10 <=> v1_funct_1(sK4)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.79/0.62  fof(f134,plain,(
% 1.79/0.62    spl6_7 <=> v1_xboole_0(sK3)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.79/0.62  fof(f114,plain,(
% 1.79/0.62    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.79/0.62  fof(f119,plain,(
% 1.79/0.62    spl6_4 <=> v1_xboole_0(sK2)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.79/0.62  fof(f109,plain,(
% 1.79/0.62    spl6_2 <=> v1_xboole_0(sK1)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.79/0.62  fof(f877,plain,(
% 1.79/0.62    spl6_121 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_121])])).
% 1.79/0.62  fof(f1165,plain,(
% 1.79/0.62    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_33 | ~spl6_47 | ~spl6_48 | ~spl6_99 | ~spl6_104 | ~spl6_121)),
% 1.79/0.62    inference(trivial_inequality_removal,[],[f1164])).
% 1.79/0.62  fof(f1164,plain,(
% 1.79/0.62    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_33 | ~spl6_47 | ~spl6_48 | ~spl6_99 | ~spl6_104 | ~spl6_121)),
% 1.79/0.62    inference(forward_demodulation,[],[f1163,f714])).
% 1.79/0.62  fof(f714,plain,(
% 1.79/0.62    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl6_99),
% 1.79/0.62    inference(avatar_component_clause,[],[f712])).
% 1.79/0.62  fof(f1163,plain,(
% 1.79/0.62    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_33 | ~spl6_47 | ~spl6_48 | ~spl6_104 | ~spl6_121)),
% 1.79/0.62    inference(forward_demodulation,[],[f1162,f747])).
% 1.79/0.62  fof(f1162,plain,(
% 1.79/0.62    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_33 | ~spl6_47 | ~spl6_48 | ~spl6_121)),
% 1.79/0.62    inference(forward_demodulation,[],[f1161,f389])).
% 1.79/0.62  fof(f1161,plain,(
% 1.79/0.62    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_33 | ~spl6_48 | ~spl6_121)),
% 1.79/0.62    inference(forward_demodulation,[],[f1160,f282])).
% 1.79/0.62  fof(f1160,plain,(
% 1.79/0.62    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_48 | ~spl6_121)),
% 1.79/0.62    inference(forward_demodulation,[],[f1159,f351])).
% 1.79/0.62  fof(f1159,plain,(
% 1.79/0.62    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_48 | ~spl6_121)),
% 1.79/0.62    inference(forward_demodulation,[],[f1135,f393])).
% 1.79/0.62  fof(f1135,plain,(
% 1.79/0.62    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~spl6_121),
% 1.79/0.62    inference(resolution,[],[f879,f100])).
% 1.79/0.62  fof(f100,plain,(
% 1.79/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 1.79/0.62    inference(equality_resolution,[],[f68])).
% 1.79/0.62  fof(f68,plain,(
% 1.79/0.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.79/0.62    inference(cnf_transformation,[],[f28])).
% 1.79/0.62  fof(f28,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.79/0.62    inference(flattening,[],[f27])).
% 1.79/0.62  fof(f27,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f20])).
% 1.79/0.62  fof(f20,axiom,(
% 1.79/0.62    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 1.79/0.62  fof(f879,plain,(
% 1.79/0.62    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl6_121),
% 1.79/0.62    inference(avatar_component_clause,[],[f877])).
% 1.79/0.62  fof(f1158,plain,(
% 1.79/0.62    spl6_15 | spl6_1 | ~spl6_117 | ~spl6_107 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_6 | spl6_7 | ~spl6_3 | spl6_4 | spl6_2 | ~spl6_6 | ~spl6_33 | ~spl6_47 | ~spl6_48 | ~spl6_99 | ~spl6_104 | ~spl6_121),
% 1.79/0.62    inference(avatar_split_clause,[],[f1157,f877,f745,f712,f392,f388,f280,f129,f109,f119,f114,f134,f129,f149,f144,f139,f164,f159,f154,f761,f841,f104,f173])).
% 1.79/0.62  fof(f173,plain,(
% 1.79/0.62    spl6_15 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.79/0.62  fof(f1157,plain,(
% 1.79/0.62    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_33 | ~spl6_47 | ~spl6_48 | ~spl6_99 | ~spl6_104 | ~spl6_121)),
% 1.79/0.62    inference(trivial_inequality_removal,[],[f1156])).
% 1.79/0.62  fof(f1156,plain,(
% 1.79/0.62    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_33 | ~spl6_47 | ~spl6_48 | ~spl6_99 | ~spl6_104 | ~spl6_121)),
% 1.79/0.62    inference(forward_demodulation,[],[f1155,f714])).
% 1.79/0.62  fof(f1155,plain,(
% 1.79/0.62    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_33 | ~spl6_47 | ~spl6_48 | ~spl6_104 | ~spl6_121)),
% 1.79/0.62    inference(forward_demodulation,[],[f1154,f747])).
% 1.79/0.62  fof(f1154,plain,(
% 1.79/0.62    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_33 | ~spl6_47 | ~spl6_48 | ~spl6_121)),
% 1.79/0.62    inference(forward_demodulation,[],[f1153,f389])).
% 1.79/0.62  fof(f1153,plain,(
% 1.79/0.62    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_33 | ~spl6_48 | ~spl6_121)),
% 1.79/0.62    inference(forward_demodulation,[],[f1152,f282])).
% 1.79/0.62  fof(f1152,plain,(
% 1.79/0.62    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_48 | ~spl6_121)),
% 1.79/0.62    inference(forward_demodulation,[],[f1151,f351])).
% 1.79/0.62  fof(f1151,plain,(
% 1.79/0.62    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_48 | ~spl6_121)),
% 1.79/0.62    inference(forward_demodulation,[],[f1134,f393])).
% 1.79/0.62  fof(f1134,plain,(
% 1.79/0.62    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~spl6_121),
% 1.79/0.62    inference(resolution,[],[f879,f101])).
% 1.79/0.62  fof(f101,plain,(
% 1.79/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 1.79/0.62    inference(equality_resolution,[],[f67])).
% 1.79/0.62  fof(f67,plain,(
% 1.79/0.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.79/0.62    inference(cnf_transformation,[],[f28])).
% 1.79/0.62  fof(f880,plain,(
% 1.79/0.62    spl6_121 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_83),
% 1.79/0.62    inference(avatar_split_clause,[],[f875,f588,f139,f144,f149,f877])).
% 1.79/0.62  fof(f588,plain,(
% 1.79/0.62    spl6_83 <=> ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).
% 1.79/0.62  fof(f875,plain,(
% 1.79/0.62    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_8 | ~spl6_83)),
% 1.79/0.62    inference(resolution,[],[f589,f141])).
% 1.79/0.62  fof(f141,plain,(
% 1.79/0.62    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl6_8),
% 1.79/0.62    inference(avatar_component_clause,[],[f139])).
% 1.79/0.62  fof(f589,plain,(
% 1.79/0.62    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))) ) | ~spl6_83),
% 1.79/0.62    inference(avatar_component_clause,[],[f588])).
% 1.79/0.62  fof(f844,plain,(
% 1.79/0.62    spl6_117 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_77),
% 1.79/0.62    inference(avatar_split_clause,[],[f839,f557,f139,f144,f149,f841])).
% 1.79/0.62  fof(f557,plain,(
% 1.79/0.62    spl6_77 <=> ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).
% 1.79/0.62  fof(f839,plain,(
% 1.79/0.62    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_8 | ~spl6_77)),
% 1.79/0.62    inference(resolution,[],[f558,f141])).
% 1.79/0.62  fof(f558,plain,(
% 1.79/0.62    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)) ) | ~spl6_77),
% 1.79/0.62    inference(avatar_component_clause,[],[f557])).
% 1.79/0.62  fof(f764,plain,(
% 1.79/0.62    spl6_107 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_71),
% 1.79/0.62    inference(avatar_split_clause,[],[f759,f524,f139,f144,f149,f761])).
% 1.79/0.62  fof(f524,plain,(
% 1.79/0.62    spl6_71 <=> ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).
% 1.79/0.62  fof(f759,plain,(
% 1.79/0.62    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_8 | ~spl6_71)),
% 1.79/0.62    inference(resolution,[],[f525,f141])).
% 1.79/0.62  fof(f525,plain,(
% 1.79/0.62    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))) ) | ~spl6_71),
% 1.79/0.62    inference(avatar_component_clause,[],[f524])).
% 1.79/0.62  fof(f748,plain,(
% 1.79/0.62    spl6_104 | ~spl6_60 | ~spl6_103),
% 1.79/0.62    inference(avatar_split_clause,[],[f740,f735,f462,f745])).
% 1.79/0.62  fof(f462,plain,(
% 1.79/0.62    spl6_60 <=> ! [X0] : (~r1_xboole_0(sK3,X0) | k1_xboole_0 = k7_relat_1(sK5,X0))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 1.79/0.62  fof(f735,plain,(
% 1.79/0.62    spl6_103 <=> r1_xboole_0(sK3,k1_xboole_0)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).
% 1.79/0.62  fof(f740,plain,(
% 1.79/0.62    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | (~spl6_60 | ~spl6_103)),
% 1.79/0.62    inference(resolution,[],[f737,f463])).
% 1.79/0.62  fof(f463,plain,(
% 1.79/0.62    ( ! [X0] : (~r1_xboole_0(sK3,X0) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl6_60),
% 1.79/0.62    inference(avatar_component_clause,[],[f462])).
% 1.79/0.62  fof(f737,plain,(
% 1.79/0.62    r1_xboole_0(sK3,k1_xboole_0) | ~spl6_103),
% 1.79/0.62    inference(avatar_component_clause,[],[f735])).
% 1.79/0.62  fof(f738,plain,(
% 1.79/0.62    spl6_103 | ~spl6_26 | ~spl6_46 | ~spl6_95),
% 1.79/0.62    inference(avatar_split_clause,[],[f733,f675,f381,f233,f735])).
% 1.79/0.62  fof(f233,plain,(
% 1.79/0.62    spl6_26 <=> v1_relat_1(sK5)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.79/0.62  fof(f381,plain,(
% 1.79/0.62    spl6_46 <=> sK3 = k1_relat_1(sK5)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 1.79/0.62  fof(f675,plain,(
% 1.79/0.62    spl6_95 <=> k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).
% 1.79/0.62  fof(f733,plain,(
% 1.79/0.62    r1_xboole_0(sK3,k1_xboole_0) | (~spl6_26 | ~spl6_46 | ~spl6_95)),
% 1.79/0.62    inference(trivial_inequality_removal,[],[f732])).
% 1.79/0.62  fof(f732,plain,(
% 1.79/0.62    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK3,k1_xboole_0) | (~spl6_26 | ~spl6_46 | ~spl6_95)),
% 1.79/0.62    inference(superposition,[],[f560,f677])).
% 1.79/0.62  fof(f677,plain,(
% 1.79/0.62    k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0) | ~spl6_95),
% 1.79/0.62    inference(avatar_component_clause,[],[f675])).
% 1.79/0.62  fof(f560,plain,(
% 1.79/0.62    ( ! [X2] : (k1_xboole_0 != k9_relat_1(sK5,X2) | r1_xboole_0(sK3,X2)) ) | (~spl6_26 | ~spl6_46)),
% 1.79/0.62    inference(forward_demodulation,[],[f308,f383])).
% 1.79/0.62  fof(f383,plain,(
% 1.79/0.62    sK3 = k1_relat_1(sK5) | ~spl6_46),
% 1.79/0.62    inference(avatar_component_clause,[],[f381])).
% 1.79/0.62  fof(f308,plain,(
% 1.79/0.62    ( ! [X2] : (r1_xboole_0(k1_relat_1(sK5),X2) | k1_xboole_0 != k9_relat_1(sK5,X2)) ) | ~spl6_26),
% 1.79/0.62    inference(resolution,[],[f79,f235])).
% 1.79/0.62  fof(f235,plain,(
% 1.79/0.62    v1_relat_1(sK5) | ~spl6_26),
% 1.79/0.62    inference(avatar_component_clause,[],[f233])).
% 1.79/0.62  fof(f79,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f37])).
% 1.79/0.62  fof(f37,plain,(
% 1.79/0.62    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.79/0.62    inference(ennf_transformation,[],[f8])).
% 1.79/0.62  fof(f8,axiom,(
% 1.79/0.62    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 1.79/0.62  fof(f715,plain,(
% 1.79/0.62    spl6_99 | ~spl6_50 | ~spl6_96),
% 1.79/0.62    inference(avatar_split_clause,[],[f707,f684,f406,f712])).
% 1.79/0.62  fof(f406,plain,(
% 1.79/0.62    spl6_50 <=> ! [X0] : (~r1_xboole_0(sK2,X0) | k1_xboole_0 = k7_relat_1(sK4,X0))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 1.79/0.62  fof(f684,plain,(
% 1.79/0.62    spl6_96 <=> r1_xboole_0(sK2,k1_xboole_0)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).
% 1.79/0.62  fof(f707,plain,(
% 1.79/0.62    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | (~spl6_50 | ~spl6_96)),
% 1.79/0.62    inference(resolution,[],[f686,f407])).
% 1.79/0.62  fof(f407,plain,(
% 1.79/0.62    ( ! [X0] : (~r1_xboole_0(sK2,X0) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl6_50),
% 1.79/0.62    inference(avatar_component_clause,[],[f406])).
% 1.79/0.62  fof(f686,plain,(
% 1.79/0.62    r1_xboole_0(sK2,k1_xboole_0) | ~spl6_96),
% 1.79/0.62    inference(avatar_component_clause,[],[f684])).
% 1.79/0.62  fof(f687,plain,(
% 1.79/0.62    spl6_96 | ~spl6_25 | ~spl6_45 | ~spl6_91),
% 1.79/0.62    inference(avatar_split_clause,[],[f682,f646,f375,f228,f684])).
% 1.79/0.62  fof(f228,plain,(
% 1.79/0.62    spl6_25 <=> v1_relat_1(sK4)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.79/0.62  fof(f375,plain,(
% 1.79/0.62    spl6_45 <=> sK2 = k1_relat_1(sK4)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 1.79/0.62  fof(f646,plain,(
% 1.79/0.62    spl6_91 <=> k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).
% 1.79/0.62  fof(f682,plain,(
% 1.79/0.62    r1_xboole_0(sK2,k1_xboole_0) | (~spl6_25 | ~spl6_45 | ~spl6_91)),
% 1.79/0.62    inference(trivial_inequality_removal,[],[f681])).
% 1.79/0.62  fof(f681,plain,(
% 1.79/0.62    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK2,k1_xboole_0) | (~spl6_25 | ~spl6_45 | ~spl6_91)),
% 1.79/0.62    inference(superposition,[],[f527,f648])).
% 1.79/0.62  fof(f648,plain,(
% 1.79/0.62    k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0) | ~spl6_91),
% 1.79/0.62    inference(avatar_component_clause,[],[f646])).
% 1.79/0.62  fof(f527,plain,(
% 1.79/0.62    ( ! [X1] : (k1_xboole_0 != k9_relat_1(sK4,X1) | r1_xboole_0(sK2,X1)) ) | (~spl6_25 | ~spl6_45)),
% 1.79/0.62    inference(forward_demodulation,[],[f307,f377])).
% 1.79/0.62  fof(f377,plain,(
% 1.79/0.62    sK2 = k1_relat_1(sK4) | ~spl6_45),
% 1.79/0.62    inference(avatar_component_clause,[],[f375])).
% 1.79/0.62  fof(f307,plain,(
% 1.79/0.62    ( ! [X1] : (r1_xboole_0(k1_relat_1(sK4),X1) | k1_xboole_0 != k9_relat_1(sK4,X1)) ) | ~spl6_25),
% 1.79/0.62    inference(resolution,[],[f79,f230])).
% 1.79/0.62  fof(f230,plain,(
% 1.79/0.62    v1_relat_1(sK4) | ~spl6_25),
% 1.79/0.62    inference(avatar_component_clause,[],[f228])).
% 1.79/0.62  fof(f678,plain,(
% 1.79/0.62    spl6_95 | ~spl6_26 | ~spl6_27 | ~spl6_68 | ~spl6_69),
% 1.79/0.62    inference(avatar_split_clause,[],[f673,f513,f506,f245,f233,f675])).
% 1.79/0.62  fof(f245,plain,(
% 1.79/0.62    spl6_27 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.79/0.62  fof(f506,plain,(
% 1.79/0.62    spl6_68 <=> k1_xboole_0 = k7_relat_1(sK5,sK2)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 1.79/0.62  fof(f513,plain,(
% 1.79/0.62    spl6_69 <=> r1_tarski(k1_xboole_0,sK2)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).
% 1.79/0.62  fof(f673,plain,(
% 1.79/0.62    k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0) | (~spl6_26 | ~spl6_27 | ~spl6_68 | ~spl6_69)),
% 1.79/0.62    inference(forward_demodulation,[],[f672,f247])).
% 1.79/0.62  fof(f247,plain,(
% 1.79/0.62    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | ~spl6_27),
% 1.79/0.62    inference(avatar_component_clause,[],[f245])).
% 1.79/0.62  fof(f672,plain,(
% 1.79/0.62    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0) | (~spl6_26 | ~spl6_68 | ~spl6_69)),
% 1.79/0.62    inference(forward_demodulation,[],[f661,f508])).
% 1.79/0.62  fof(f508,plain,(
% 1.79/0.62    k1_xboole_0 = k7_relat_1(sK5,sK2) | ~spl6_68),
% 1.79/0.62    inference(avatar_component_clause,[],[f506])).
% 1.79/0.62  fof(f661,plain,(
% 1.79/0.62    k9_relat_1(sK5,k1_xboole_0) = k9_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0) | (~spl6_26 | ~spl6_69)),
% 1.79/0.62    inference(resolution,[],[f358,f515])).
% 1.79/0.62  fof(f515,plain,(
% 1.79/0.62    r1_tarski(k1_xboole_0,sK2) | ~spl6_69),
% 1.79/0.62    inference(avatar_component_clause,[],[f513])).
% 1.79/0.62  fof(f358,plain,(
% 1.79/0.62    ( ! [X4,X5] : (~r1_tarski(X4,X5) | k9_relat_1(k7_relat_1(sK5,X5),X4) = k9_relat_1(sK5,X4)) ) | ~spl6_26),
% 1.79/0.62    inference(resolution,[],[f72,f235])).
% 1.79/0.62  fof(f72,plain,(
% 1.79/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f31])).
% 1.79/0.62  fof(f31,plain,(
% 1.79/0.62    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f9])).
% 1.79/0.62  fof(f9,axiom,(
% 1.79/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 1.79/0.62  fof(f649,plain,(
% 1.79/0.62    spl6_91 | ~spl6_25 | ~spl6_27 | ~spl6_65 | ~spl6_66),
% 1.79/0.62    inference(avatar_split_clause,[],[f644,f494,f487,f245,f228,f646])).
% 1.79/0.62  fof(f487,plain,(
% 1.79/0.62    spl6_65 <=> k1_xboole_0 = k7_relat_1(sK4,sK3)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 1.79/0.62  fof(f494,plain,(
% 1.79/0.62    spl6_66 <=> r1_tarski(k1_xboole_0,sK3)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).
% 1.79/0.62  fof(f644,plain,(
% 1.79/0.62    k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0) | (~spl6_25 | ~spl6_27 | ~spl6_65 | ~spl6_66)),
% 1.79/0.62    inference(forward_demodulation,[],[f643,f247])).
% 1.79/0.62  fof(f643,plain,(
% 1.79/0.62    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0) | (~spl6_25 | ~spl6_65 | ~spl6_66)),
% 1.79/0.62    inference(forward_demodulation,[],[f636,f489])).
% 1.79/0.62  fof(f489,plain,(
% 1.79/0.62    k1_xboole_0 = k7_relat_1(sK4,sK3) | ~spl6_65),
% 1.79/0.62    inference(avatar_component_clause,[],[f487])).
% 1.79/0.62  fof(f636,plain,(
% 1.79/0.62    k9_relat_1(sK4,k1_xboole_0) = k9_relat_1(k7_relat_1(sK4,sK3),k1_xboole_0) | (~spl6_25 | ~spl6_66)),
% 1.79/0.62    inference(resolution,[],[f357,f496])).
% 1.79/0.62  fof(f496,plain,(
% 1.79/0.62    r1_tarski(k1_xboole_0,sK3) | ~spl6_66),
% 1.79/0.62    inference(avatar_component_clause,[],[f494])).
% 1.79/0.62  fof(f357,plain,(
% 1.79/0.62    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k9_relat_1(k7_relat_1(sK4,X3),X2) = k9_relat_1(sK4,X2)) ) | ~spl6_25),
% 1.79/0.62    inference(resolution,[],[f72,f230])).
% 1.79/0.62  fof(f590,plain,(
% 1.79/0.62    ~spl6_6 | ~spl6_12 | spl6_7 | ~spl6_13 | spl6_2 | spl6_83 | ~spl6_11 | ~spl6_63),
% 1.79/0.62    inference(avatar_split_clause,[],[f582,f478,f154,f588,f109,f164,f134,f159,f129])).
% 1.79/0.62  fof(f478,plain,(
% 1.79/0.62    spl6_63 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 1.79/0.62  fof(f582,plain,(
% 1.79/0.62    ( ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl6_11 | ~spl6_63)),
% 1.79/0.62    inference(resolution,[],[f479,f156])).
% 1.79/0.62  fof(f156,plain,(
% 1.79/0.62    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl6_11),
% 1.79/0.62    inference(avatar_component_clause,[],[f154])).
% 1.79/0.62  fof(f479,plain,(
% 1.79/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl6_63),
% 1.79/0.62    inference(avatar_component_clause,[],[f478])).
% 1.79/0.62  fof(f559,plain,(
% 1.79/0.62    ~spl6_6 | ~spl6_12 | spl6_7 | ~spl6_13 | spl6_2 | spl6_77 | ~spl6_11 | ~spl6_57),
% 1.79/0.62    inference(avatar_split_clause,[],[f551,f444,f154,f557,f109,f164,f134,f159,f129])).
% 1.79/0.62  fof(f444,plain,(
% 1.79/0.62    spl6_57 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 1.79/0.62  fof(f551,plain,(
% 1.79/0.62    ( ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl6_11 | ~spl6_57)),
% 1.79/0.62    inference(resolution,[],[f445,f156])).
% 1.79/0.62  fof(f445,plain,(
% 1.79/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl6_57),
% 1.79/0.62    inference(avatar_component_clause,[],[f444])).
% 1.79/0.62  fof(f526,plain,(
% 1.79/0.62    ~spl6_6 | ~spl6_12 | spl6_7 | ~spl6_13 | spl6_2 | spl6_71 | ~spl6_11 | ~spl6_53),
% 1.79/0.62    inference(avatar_split_clause,[],[f518,f422,f154,f524,f109,f164,f134,f159,f129])).
% 1.79/0.62  fof(f422,plain,(
% 1.79/0.62    spl6_53 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 1.79/0.62  fof(f518,plain,(
% 1.79/0.62    ( ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl6_11 | ~spl6_53)),
% 1.79/0.62    inference(resolution,[],[f423,f156])).
% 1.79/0.62  fof(f423,plain,(
% 1.79/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl6_53),
% 1.79/0.62    inference(avatar_component_clause,[],[f422])).
% 1.79/0.62  fof(f516,plain,(
% 1.79/0.62    spl6_69 | ~spl6_19 | ~spl6_26 | ~spl6_68),
% 1.79/0.62    inference(avatar_split_clause,[],[f511,f506,f233,f192,f513])).
% 1.79/0.62  fof(f192,plain,(
% 1.79/0.62    spl6_19 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.79/0.62  fof(f511,plain,(
% 1.79/0.62    r1_tarski(k1_xboole_0,sK2) | (~spl6_19 | ~spl6_26 | ~spl6_68)),
% 1.79/0.62    inference(forward_demodulation,[],[f510,f194])).
% 1.79/0.62  fof(f194,plain,(
% 1.79/0.62    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_19),
% 1.79/0.62    inference(avatar_component_clause,[],[f192])).
% 1.79/0.62  fof(f510,plain,(
% 1.79/0.62    r1_tarski(k1_relat_1(k1_xboole_0),sK2) | (~spl6_26 | ~spl6_68)),
% 1.79/0.62    inference(superposition,[],[f238,f508])).
% 1.79/0.62  fof(f238,plain,(
% 1.79/0.62    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),X0)) ) | ~spl6_26),
% 1.79/0.62    inference(resolution,[],[f235,f77])).
% 1.79/0.62  fof(f77,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f36])).
% 1.79/0.62  fof(f36,plain,(
% 1.79/0.62    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.79/0.62    inference(ennf_transformation,[],[f12])).
% 1.79/0.62  fof(f12,axiom,(
% 1.79/0.62    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.79/0.62  fof(f509,plain,(
% 1.79/0.62    spl6_68 | ~spl6_32 | ~spl6_62),
% 1.79/0.62    inference(avatar_split_clause,[],[f504,f470,f273,f506])).
% 1.79/0.62  fof(f273,plain,(
% 1.79/0.62    spl6_32 <=> r1_xboole_0(sK2,sK3)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 1.79/0.62  fof(f470,plain,(
% 1.79/0.62    spl6_62 <=> ! [X2] : (~r1_xboole_0(X2,sK3) | k1_xboole_0 = k7_relat_1(sK5,X2))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 1.79/0.62  fof(f504,plain,(
% 1.79/0.62    k1_xboole_0 = k7_relat_1(sK5,sK2) | (~spl6_32 | ~spl6_62)),
% 1.79/0.62    inference(resolution,[],[f471,f275])).
% 1.79/0.62  fof(f275,plain,(
% 1.79/0.62    r1_xboole_0(sK2,sK3) | ~spl6_32),
% 1.79/0.62    inference(avatar_component_clause,[],[f273])).
% 1.79/0.62  fof(f471,plain,(
% 1.79/0.62    ( ! [X2] : (~r1_xboole_0(X2,sK3) | k1_xboole_0 = k7_relat_1(sK5,X2)) ) | ~spl6_62),
% 1.79/0.62    inference(avatar_component_clause,[],[f470])).
% 1.79/0.62  fof(f497,plain,(
% 1.79/0.62    spl6_66 | ~spl6_19 | ~spl6_25 | ~spl6_65),
% 1.79/0.62    inference(avatar_split_clause,[],[f492,f487,f228,f192,f494])).
% 1.79/0.62  fof(f492,plain,(
% 1.79/0.62    r1_tarski(k1_xboole_0,sK3) | (~spl6_19 | ~spl6_25 | ~spl6_65)),
% 1.79/0.62    inference(forward_demodulation,[],[f491,f194])).
% 1.79/0.62  fof(f491,plain,(
% 1.79/0.62    r1_tarski(k1_relat_1(k1_xboole_0),sK3) | (~spl6_25 | ~spl6_65)),
% 1.79/0.62    inference(superposition,[],[f237,f489])).
% 1.79/0.62  fof(f237,plain,(
% 1.79/0.62    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0)) ) | ~spl6_25),
% 1.79/0.62    inference(resolution,[],[f230,f77])).
% 1.79/0.62  fof(f490,plain,(
% 1.79/0.62    spl6_65 | ~spl6_32 | ~spl6_50),
% 1.79/0.62    inference(avatar_split_clause,[],[f485,f406,f273,f487])).
% 1.79/0.62  fof(f485,plain,(
% 1.79/0.62    k1_xboole_0 = k7_relat_1(sK4,sK3) | (~spl6_32 | ~spl6_50)),
% 1.79/0.62    inference(resolution,[],[f407,f275])).
% 1.79/0.62  fof(f480,plain,(
% 1.79/0.62    spl6_1 | spl6_4 | spl6_63 | ~spl6_3),
% 1.79/0.62    inference(avatar_split_clause,[],[f473,f114,f478,f119,f104])).
% 1.79/0.62  fof(f473,plain,(
% 1.79/0.62    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0)))) ) | ~spl6_3),
% 1.79/0.62    inference(resolution,[],[f94,f116])).
% 1.79/0.62  fof(f116,plain,(
% 1.79/0.62    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl6_3),
% 1.79/0.62    inference(avatar_component_clause,[],[f114])).
% 1.79/0.62  fof(f94,plain,(
% 1.79/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 1.79/0.62    inference(cnf_transformation,[],[f49])).
% 1.79/0.62  fof(f49,plain,(
% 1.79/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.79/0.62    inference(flattening,[],[f48])).
% 1.79/0.62  fof(f48,plain,(
% 1.79/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f21])).
% 1.79/0.62  fof(f21,axiom,(
% 1.79/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 1.79/0.62  fof(f472,plain,(
% 1.79/0.62    ~spl6_26 | spl6_62 | ~spl6_46),
% 1.79/0.62    inference(avatar_split_clause,[],[f454,f381,f470,f233])).
% 1.79/0.62  fof(f454,plain,(
% 1.79/0.62    ( ! [X2] : (~r1_xboole_0(X2,sK3) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X2)) ) | ~spl6_46),
% 1.79/0.62    inference(superposition,[],[f71,f383])).
% 1.79/0.62  fof(f71,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f30])).
% 1.79/0.62  fof(f30,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f10])).
% 1.79/0.62  fof(f10,axiom,(
% 1.79/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 1.79/0.62  fof(f464,plain,(
% 1.79/0.62    ~spl6_26 | spl6_60 | ~spl6_46),
% 1.79/0.62    inference(avatar_split_clause,[],[f452,f381,f462,f233])).
% 1.79/0.62  fof(f452,plain,(
% 1.79/0.62    ( ! [X0] : (~r1_xboole_0(sK3,X0) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl6_46),
% 1.79/0.62    inference(superposition,[],[f80,f383])).
% 1.79/0.62  fof(f80,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f38])).
% 1.79/0.62  fof(f38,plain,(
% 1.79/0.62    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.79/0.62    inference(ennf_transformation,[],[f13])).
% 1.79/0.62  fof(f13,axiom,(
% 1.79/0.62    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 1.79/0.62  fof(f446,plain,(
% 1.79/0.62    spl6_1 | spl6_4 | spl6_57 | ~spl6_3),
% 1.79/0.62    inference(avatar_split_clause,[],[f439,f114,f444,f119,f104])).
% 1.79/0.62  fof(f439,plain,(
% 1.79/0.62    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0)) ) | ~spl6_3),
% 1.79/0.62    inference(resolution,[],[f93,f116])).
% 1.79/0.62  fof(f93,plain,(
% 1.79/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f49])).
% 1.79/0.62  fof(f424,plain,(
% 1.79/0.62    spl6_1 | spl6_4 | spl6_53 | ~spl6_3),
% 1.79/0.62    inference(avatar_split_clause,[],[f417,f114,f422,f119,f104])).
% 1.79/0.62  fof(f417,plain,(
% 1.79/0.62    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3))) ) | ~spl6_3),
% 1.79/0.62    inference(resolution,[],[f92,f116])).
% 1.79/0.62  fof(f92,plain,(
% 1.79/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 1.79/0.62    inference(cnf_transformation,[],[f49])).
% 1.79/0.62  fof(f408,plain,(
% 1.79/0.62    ~spl6_25 | spl6_50 | ~spl6_45),
% 1.79/0.62    inference(avatar_split_clause,[],[f396,f375,f406,f228])).
% 1.79/0.62  fof(f396,plain,(
% 1.79/0.62    ( ! [X0] : (~r1_xboole_0(sK2,X0) | ~v1_relat_1(sK4) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl6_45),
% 1.79/0.62    inference(superposition,[],[f80,f377])).
% 1.79/0.62  fof(f394,plain,(
% 1.79/0.62    spl6_48 | ~spl6_13 | ~spl6_11),
% 1.79/0.62    inference(avatar_split_clause,[],[f386,f154,f164,f392])).
% 1.79/0.62  fof(f386,plain,(
% 1.79/0.62    ( ! [X1] : (~v1_funct_1(sK5) | k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1)) ) | ~spl6_11),
% 1.79/0.62    inference(resolution,[],[f91,f156])).
% 1.79/0.62  fof(f91,plain,(
% 1.79/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f47])).
% 1.79/0.62  fof(f47,plain,(
% 1.79/0.62    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.79/0.62    inference(flattening,[],[f46])).
% 1.79/0.62  fof(f46,plain,(
% 1.79/0.62    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.79/0.62    inference(ennf_transformation,[],[f19])).
% 1.79/0.62  fof(f19,axiom,(
% 1.79/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.79/0.62  fof(f390,plain,(
% 1.79/0.62    spl6_47 | ~spl6_10 | ~spl6_8),
% 1.79/0.62    inference(avatar_split_clause,[],[f385,f139,f149,f388])).
% 1.79/0.62  fof(f385,plain,(
% 1.79/0.62    ( ! [X0] : (~v1_funct_1(sK4) | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl6_8),
% 1.79/0.62    inference(resolution,[],[f91,f141])).
% 1.79/0.62  fof(f384,plain,(
% 1.79/0.62    ~spl6_26 | spl6_46 | ~spl6_31 | ~spl6_44),
% 1.79/0.62    inference(avatar_split_clause,[],[f379,f369,f267,f381,f233])).
% 1.79/0.62  fof(f267,plain,(
% 1.79/0.62    spl6_31 <=> v4_relat_1(sK5,sK3)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 1.79/0.62  fof(f369,plain,(
% 1.79/0.62    spl6_44 <=> v1_partfun1(sK5,sK3)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 1.79/0.62  fof(f379,plain,(
% 1.79/0.62    ~v4_relat_1(sK5,sK3) | sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5) | ~spl6_44),
% 1.79/0.62    inference(resolution,[],[f371,f85])).
% 1.79/0.62  fof(f85,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f42])).
% 1.79/0.62  fof(f42,plain,(
% 1.79/0.62    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.79/0.62    inference(flattening,[],[f41])).
% 1.79/0.62  fof(f41,plain,(
% 1.79/0.62    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.79/0.62    inference(ennf_transformation,[],[f18])).
% 1.79/0.62  fof(f18,axiom,(
% 1.79/0.62    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 1.79/0.62  fof(f371,plain,(
% 1.79/0.62    v1_partfun1(sK5,sK3) | ~spl6_44),
% 1.79/0.62    inference(avatar_component_clause,[],[f369])).
% 1.79/0.62  fof(f378,plain,(
% 1.79/0.62    ~spl6_25 | spl6_45 | ~spl6_30 | ~spl6_43),
% 1.79/0.62    inference(avatar_split_clause,[],[f373,f364,f262,f375,f228])).
% 1.79/0.62  fof(f262,plain,(
% 1.79/0.62    spl6_30 <=> v4_relat_1(sK4,sK2)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 1.79/0.62  fof(f364,plain,(
% 1.79/0.62    spl6_43 <=> v1_partfun1(sK4,sK2)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 1.79/0.62  fof(f373,plain,(
% 1.79/0.62    ~v4_relat_1(sK4,sK2) | sK2 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl6_43),
% 1.79/0.62    inference(resolution,[],[f366,f85])).
% 1.79/0.62  fof(f366,plain,(
% 1.79/0.62    v1_partfun1(sK4,sK2) | ~spl6_43),
% 1.79/0.62    inference(avatar_component_clause,[],[f364])).
% 1.79/0.62  fof(f372,plain,(
% 1.79/0.62    spl6_44 | ~spl6_12 | ~spl6_13 | spl6_2 | ~spl6_11),
% 1.79/0.62    inference(avatar_split_clause,[],[f362,f154,f109,f164,f159,f369])).
% 1.79/0.62  fof(f362,plain,(
% 1.79/0.62    v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3) | ~spl6_11),
% 1.79/0.62    inference(resolution,[],[f76,f156])).
% 1.79/0.62  fof(f76,plain,(
% 1.79/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f35])).
% 1.79/0.62  fof(f35,plain,(
% 1.79/0.62    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.79/0.62    inference(flattening,[],[f34])).
% 1.79/0.62  fof(f34,plain,(
% 1.79/0.62    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.79/0.62    inference(ennf_transformation,[],[f17])).
% 1.79/0.62  fof(f17,axiom,(
% 1.79/0.62    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.79/0.62  fof(f367,plain,(
% 1.79/0.62    spl6_43 | ~spl6_9 | ~spl6_10 | spl6_2 | ~spl6_8),
% 1.79/0.62    inference(avatar_split_clause,[],[f361,f139,f109,f149,f144,f364])).
% 1.79/0.62  fof(f361,plain,(
% 1.79/0.62    v1_xboole_0(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2) | ~spl6_8),
% 1.79/0.62    inference(resolution,[],[f76,f141])).
% 1.79/0.62  fof(f283,plain,(
% 1.79/0.62    spl6_33 | ~spl6_32),
% 1.79/0.62    inference(avatar_split_clause,[],[f278,f273,f280])).
% 1.79/0.62  fof(f278,plain,(
% 1.79/0.62    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl6_32),
% 1.79/0.62    inference(resolution,[],[f275,f95])).
% 1.79/0.62  fof(f95,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.79/0.62    inference(definition_unfolding,[],[f87,f75])).
% 1.79/0.62  fof(f87,plain,(
% 1.79/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.79/0.63    inference(cnf_transformation,[],[f1])).
% 1.79/0.63  fof(f1,axiom,(
% 1.79/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.79/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.79/0.63  fof(f276,plain,(
% 1.79/0.63    spl6_4 | spl6_32 | spl6_7 | ~spl6_5),
% 1.79/0.63    inference(avatar_split_clause,[],[f271,f124,f134,f273,f119])).
% 1.79/0.63  fof(f124,plain,(
% 1.79/0.63    spl6_5 <=> r1_subset_1(sK2,sK3)),
% 1.79/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.79/0.63  fof(f271,plain,(
% 1.79/0.63    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | ~spl6_5),
% 1.79/0.63    inference(resolution,[],[f83,f126])).
% 1.79/0.63  fof(f126,plain,(
% 1.79/0.63    r1_subset_1(sK2,sK3) | ~spl6_5),
% 1.79/0.63    inference(avatar_component_clause,[],[f124])).
% 1.79/0.63  fof(f83,plain,(
% 1.79/0.63    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 1.79/0.63    inference(cnf_transformation,[],[f40])).
% 1.79/0.63  fof(f40,plain,(
% 1.79/0.63    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.79/0.63    inference(flattening,[],[f39])).
% 1.79/0.63  fof(f39,plain,(
% 1.79/0.63    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.79/0.63    inference(ennf_transformation,[],[f14])).
% 1.79/0.63  fof(f14,axiom,(
% 1.79/0.63    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 1.79/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 1.79/0.63  fof(f270,plain,(
% 1.79/0.63    spl6_31 | ~spl6_11),
% 1.79/0.63    inference(avatar_split_clause,[],[f260,f154,f267])).
% 1.79/0.63  fof(f260,plain,(
% 1.79/0.63    v4_relat_1(sK5,sK3) | ~spl6_11),
% 1.79/0.63    inference(resolution,[],[f90,f156])).
% 1.79/0.63  fof(f90,plain,(
% 1.79/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.79/0.63    inference(cnf_transformation,[],[f45])).
% 1.79/0.63  fof(f45,plain,(
% 1.79/0.63    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.79/0.63    inference(ennf_transformation,[],[f24])).
% 1.79/0.63  fof(f24,plain,(
% 1.79/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.79/0.63    inference(pure_predicate_removal,[],[f16])).
% 1.79/0.63  fof(f16,axiom,(
% 1.79/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.79/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.79/0.63  fof(f265,plain,(
% 1.79/0.63    spl6_30 | ~spl6_8),
% 1.79/0.63    inference(avatar_split_clause,[],[f259,f139,f262])).
% 1.79/0.63  fof(f259,plain,(
% 1.79/0.63    v4_relat_1(sK4,sK2) | ~spl6_8),
% 1.79/0.63    inference(resolution,[],[f90,f141])).
% 1.79/0.63  fof(f248,plain,(
% 1.79/0.63    spl6_27 | ~spl6_18 | ~spl6_19 | ~spl6_20),
% 1.79/0.63    inference(avatar_split_clause,[],[f243,f198,f192,f187,f245])).
% 1.79/0.63  fof(f187,plain,(
% 1.79/0.63    spl6_18 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.79/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.79/0.63  fof(f198,plain,(
% 1.79/0.63    spl6_20 <=> v1_relat_1(k1_xboole_0)),
% 1.79/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.79/0.63  fof(f243,plain,(
% 1.79/0.63    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | (~spl6_18 | ~spl6_19 | ~spl6_20)),
% 1.79/0.63    inference(forward_demodulation,[],[f242,f189])).
% 1.79/0.63  fof(f189,plain,(
% 1.79/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl6_18),
% 1.79/0.63    inference(avatar_component_clause,[],[f187])).
% 1.79/0.63  fof(f242,plain,(
% 1.79/0.63    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) | (~spl6_19 | ~spl6_20)),
% 1.79/0.63    inference(forward_demodulation,[],[f239,f194])).
% 1.79/0.63  fof(f239,plain,(
% 1.79/0.63    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) | ~spl6_20),
% 1.79/0.63    inference(resolution,[],[f70,f200])).
% 1.79/0.63  fof(f200,plain,(
% 1.79/0.63    v1_relat_1(k1_xboole_0) | ~spl6_20),
% 1.79/0.63    inference(avatar_component_clause,[],[f198])).
% 1.79/0.63  fof(f70,plain,(
% 1.79/0.63    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.79/0.63    inference(cnf_transformation,[],[f29])).
% 1.79/0.63  fof(f29,plain,(
% 1.79/0.63    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.79/0.63    inference(ennf_transformation,[],[f7])).
% 1.79/0.63  fof(f7,axiom,(
% 1.79/0.63    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.79/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.79/0.63  fof(f236,plain,(
% 1.79/0.63    spl6_26 | ~spl6_11),
% 1.79/0.63    inference(avatar_split_clause,[],[f226,f154,f233])).
% 1.79/0.63  fof(f226,plain,(
% 1.79/0.63    v1_relat_1(sK5) | ~spl6_11),
% 1.79/0.63    inference(resolution,[],[f89,f156])).
% 1.79/0.63  fof(f89,plain,(
% 1.79/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.79/0.63    inference(cnf_transformation,[],[f44])).
% 1.79/0.63  fof(f44,plain,(
% 1.79/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.79/0.63    inference(ennf_transformation,[],[f15])).
% 1.79/0.63  fof(f15,axiom,(
% 1.79/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.79/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.79/0.63  fof(f231,plain,(
% 1.79/0.63    spl6_25 | ~spl6_8),
% 1.79/0.63    inference(avatar_split_clause,[],[f225,f139,f228])).
% 1.79/0.63  fof(f225,plain,(
% 1.79/0.63    v1_relat_1(sK4) | ~spl6_8),
% 1.79/0.63    inference(resolution,[],[f89,f141])).
% 1.79/0.63  fof(f201,plain,(
% 1.79/0.63    spl6_20 | ~spl6_17),
% 1.79/0.63    inference(avatar_split_clause,[],[f196,f182,f198])).
% 1.79/0.63  fof(f182,plain,(
% 1.79/0.63    spl6_17 <=> v1_xboole_0(k1_xboole_0)),
% 1.79/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.79/0.63  fof(f196,plain,(
% 1.79/0.63    v1_relat_1(k1_xboole_0) | ~spl6_17),
% 1.79/0.63    inference(resolution,[],[f73,f184])).
% 1.79/0.63  fof(f184,plain,(
% 1.79/0.63    v1_xboole_0(k1_xboole_0) | ~spl6_17),
% 1.79/0.63    inference(avatar_component_clause,[],[f182])).
% 1.79/0.63  fof(f73,plain,(
% 1.79/0.63    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 1.79/0.63    inference(cnf_transformation,[],[f32])).
% 1.79/0.63  fof(f32,plain,(
% 1.79/0.63    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.79/0.63    inference(ennf_transformation,[],[f6])).
% 1.79/0.63  fof(f6,axiom,(
% 1.79/0.63    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.79/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.79/0.63  fof(f195,plain,(
% 1.79/0.63    spl6_19),
% 1.79/0.63    inference(avatar_split_clause,[],[f65,f192])).
% 1.79/0.63  fof(f65,plain,(
% 1.79/0.63    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.79/0.63    inference(cnf_transformation,[],[f11])).
% 1.79/0.63  fof(f11,axiom,(
% 1.79/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.79/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.79/0.63  fof(f190,plain,(
% 1.79/0.63    spl6_18),
% 1.79/0.63    inference(avatar_split_clause,[],[f66,f187])).
% 1.79/0.63  fof(f66,plain,(
% 1.79/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.79/0.63    inference(cnf_transformation,[],[f11])).
% 1.79/0.63  fof(f185,plain,(
% 1.79/0.63    spl6_17),
% 1.79/0.63    inference(avatar_split_clause,[],[f64,f182])).
% 1.79/0.63  fof(f64,plain,(
% 1.79/0.63    v1_xboole_0(k1_xboole_0)),
% 1.79/0.63    inference(cnf_transformation,[],[f2])).
% 1.79/0.63  fof(f2,axiom,(
% 1.79/0.63    v1_xboole_0(k1_xboole_0)),
% 1.79/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.79/0.63  fof(f180,plain,(
% 1.79/0.63    ~spl6_14 | ~spl6_15 | ~spl6_16),
% 1.79/0.63    inference(avatar_split_clause,[],[f50,f177,f173,f169])).
% 1.79/0.63  fof(f50,plain,(
% 1.79/0.63    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.79/0.63    inference(cnf_transformation,[],[f26])).
% 1.79/0.63  fof(f26,plain,(
% 1.79/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.79/0.63    inference(flattening,[],[f25])).
% 1.79/0.63  fof(f25,plain,(
% 1.79/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.79/0.63    inference(ennf_transformation,[],[f23])).
% 1.79/0.63  fof(f23,negated_conjecture,(
% 1.79/0.63    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.79/0.63    inference(negated_conjecture,[],[f22])).
% 1.79/0.63  fof(f22,conjecture,(
% 1.79/0.63    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.79/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 1.79/0.63  fof(f167,plain,(
% 1.79/0.63    spl6_13),
% 1.79/0.63    inference(avatar_split_clause,[],[f51,f164])).
% 1.79/0.63  fof(f51,plain,(
% 1.79/0.63    v1_funct_1(sK5)),
% 1.79/0.63    inference(cnf_transformation,[],[f26])).
% 1.79/0.63  fof(f162,plain,(
% 1.79/0.63    spl6_12),
% 1.79/0.63    inference(avatar_split_clause,[],[f52,f159])).
% 1.79/0.63  fof(f52,plain,(
% 1.79/0.63    v1_funct_2(sK5,sK3,sK1)),
% 1.79/0.63    inference(cnf_transformation,[],[f26])).
% 1.79/0.63  fof(f157,plain,(
% 1.79/0.63    spl6_11),
% 1.79/0.63    inference(avatar_split_clause,[],[f53,f154])).
% 1.79/0.63  fof(f53,plain,(
% 1.79/0.63    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.79/0.63    inference(cnf_transformation,[],[f26])).
% 1.79/0.63  fof(f152,plain,(
% 1.79/0.63    spl6_10),
% 1.79/0.63    inference(avatar_split_clause,[],[f54,f149])).
% 1.79/0.63  fof(f54,plain,(
% 1.79/0.63    v1_funct_1(sK4)),
% 1.79/0.63    inference(cnf_transformation,[],[f26])).
% 1.79/0.63  fof(f147,plain,(
% 1.79/0.63    spl6_9),
% 1.79/0.63    inference(avatar_split_clause,[],[f55,f144])).
% 1.79/0.63  fof(f55,plain,(
% 1.79/0.63    v1_funct_2(sK4,sK2,sK1)),
% 1.79/0.63    inference(cnf_transformation,[],[f26])).
% 1.79/0.63  fof(f142,plain,(
% 1.79/0.63    spl6_8),
% 1.79/0.63    inference(avatar_split_clause,[],[f56,f139])).
% 1.79/0.63  fof(f56,plain,(
% 1.79/0.63    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.79/0.63    inference(cnf_transformation,[],[f26])).
% 1.79/0.63  fof(f137,plain,(
% 1.79/0.63    ~spl6_7),
% 1.79/0.63    inference(avatar_split_clause,[],[f57,f134])).
% 1.79/0.63  fof(f57,plain,(
% 1.79/0.63    ~v1_xboole_0(sK3)),
% 1.79/0.63    inference(cnf_transformation,[],[f26])).
% 1.79/0.63  fof(f132,plain,(
% 1.79/0.63    spl6_6),
% 1.79/0.63    inference(avatar_split_clause,[],[f58,f129])).
% 1.79/0.63  fof(f58,plain,(
% 1.79/0.63    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.79/0.63    inference(cnf_transformation,[],[f26])).
% 1.79/0.63  fof(f127,plain,(
% 1.79/0.63    spl6_5),
% 1.79/0.63    inference(avatar_split_clause,[],[f59,f124])).
% 1.79/0.63  fof(f59,plain,(
% 1.79/0.63    r1_subset_1(sK2,sK3)),
% 1.79/0.63    inference(cnf_transformation,[],[f26])).
% 1.79/0.63  fof(f122,plain,(
% 1.79/0.63    ~spl6_4),
% 1.79/0.63    inference(avatar_split_clause,[],[f60,f119])).
% 1.79/0.63  fof(f60,plain,(
% 1.79/0.63    ~v1_xboole_0(sK2)),
% 1.79/0.63    inference(cnf_transformation,[],[f26])).
% 1.79/0.63  fof(f117,plain,(
% 1.79/0.63    spl6_3),
% 1.79/0.63    inference(avatar_split_clause,[],[f61,f114])).
% 1.79/0.63  fof(f61,plain,(
% 1.79/0.63    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.79/0.63    inference(cnf_transformation,[],[f26])).
% 1.79/0.63  fof(f112,plain,(
% 1.79/0.63    ~spl6_2),
% 1.79/0.63    inference(avatar_split_clause,[],[f62,f109])).
% 1.79/0.63  fof(f62,plain,(
% 1.79/0.63    ~v1_xboole_0(sK1)),
% 1.79/0.63    inference(cnf_transformation,[],[f26])).
% 1.79/0.63  fof(f107,plain,(
% 1.79/0.63    ~spl6_1),
% 1.79/0.63    inference(avatar_split_clause,[],[f63,f104])).
% 1.79/0.63  fof(f63,plain,(
% 1.79/0.63    ~v1_xboole_0(sK0)),
% 1.79/0.63    inference(cnf_transformation,[],[f26])).
% 1.79/0.63  % SZS output end Proof for theBenchmark
% 1.79/0.63  % (9180)------------------------------
% 1.79/0.63  % (9180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.63  % (9180)Termination reason: Refutation
% 1.79/0.63  
% 1.79/0.63  % (9180)Memory used [KB]: 11769
% 1.79/0.63  % (9180)Time elapsed: 0.187 s
% 1.79/0.63  % (9180)------------------------------
% 1.79/0.63  % (9180)------------------------------
% 1.79/0.63  % (9163)Success in time 0.256 s
%------------------------------------------------------------------------------
