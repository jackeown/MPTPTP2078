%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:30 EST 2020

% Result     : Theorem 2.01s
% Output     : Refutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  312 ( 702 expanded)
%              Number of leaves         :   74 ( 343 expanded)
%              Depth                    :   14
%              Number of atoms          : 1510 (3259 expanded)
%              Number of equality atoms :  176 ( 472 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1273,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f111,f116,f121,f126,f131,f136,f141,f146,f151,f156,f161,f166,f179,f184,f189,f228,f233,f238,f261,f269,f274,f280,f287,f377,f382,f396,f403,f407,f413,f422,f443,f461,f478,f496,f504,f510,f517,f529,f536,f548,f583,f616,f655,f704,f711,f739,f765,f772,f782,f861,f914,f1186,f1194,f1272])).

fof(f1272,plain,
    ( ~ spl6_102
    | ~ spl6_6
    | spl6_16
    | ~ spl6_34
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_108 ),
    inference(avatar_split_clause,[],[f1271,f779,f405,f401,f284,f176,f128,f736])).

fof(f736,plain,
    ( spl6_102
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).

fof(f128,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f176,plain,
    ( spl6_16
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f284,plain,
    ( spl6_34
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f401,plain,
    ( spl6_49
  <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f405,plain,
    ( spl6_50
  <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f779,plain,
    ( spl6_108
  <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_108])])).

fof(f1271,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_6
    | spl6_16
    | ~ spl6_34
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_108 ),
    inference(forward_demodulation,[],[f1270,f781])).

fof(f781,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_108 ),
    inference(avatar_component_clause,[],[f779])).

fof(f1270,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_6
    | spl6_16
    | ~ spl6_34
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(forward_demodulation,[],[f1269,f402])).

fof(f402,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f401])).

fof(f1269,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl6_6
    | spl6_16
    | ~ spl6_34
    | ~ spl6_50 ),
    inference(forward_demodulation,[],[f1268,f286])).

fof(f286,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f284])).

fof(f1268,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl6_6
    | spl6_16
    | ~ spl6_50 ),
    inference(forward_demodulation,[],[f1267,f359])).

fof(f359,plain,
    ( ! [X1] : k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))
    | ~ spl6_6 ),
    inference(resolution,[],[f96,f130])).

fof(f130,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f87,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f1267,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_16
    | ~ spl6_50 ),
    inference(forward_demodulation,[],[f178,f406])).

fof(f406,plain,
    ( ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f405])).

fof(f178,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f176])).

fof(f1194,plain,
    ( spl6_14
    | spl6_1
    | ~ spl6_118
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
    | ~ spl6_34
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_102
    | ~ spl6_108
    | ~ spl6_124 ),
    inference(avatar_split_clause,[],[f1193,f911,f779,f736,f405,f401,f284,f128,f108,f118,f113,f133,f128,f148,f143,f138,f163,f158,f153,f769,f858,f103,f168])).

fof(f168,plain,
    ( spl6_14
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f103,plain,
    ( spl6_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f858,plain,
    ( spl6_118
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).

fof(f769,plain,
    ( spl6_107
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).

fof(f153,plain,
    ( spl6_11
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f158,plain,
    ( spl6_12
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f163,plain,
    ( spl6_13
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f138,plain,
    ( spl6_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f143,plain,
    ( spl6_9
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f148,plain,
    ( spl6_10
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f133,plain,
    ( spl6_7
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f113,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f118,plain,
    ( spl6_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f108,plain,
    ( spl6_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f911,plain,
    ( spl6_124
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_124])])).

fof(f1193,plain,
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
    | ~ spl6_34
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_102
    | ~ spl6_108
    | ~ spl6_124 ),
    inference(trivial_inequality_removal,[],[f1192])).

fof(f1192,plain,
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
    | ~ spl6_34
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_102
    | ~ spl6_108
    | ~ spl6_124 ),
    inference(forward_demodulation,[],[f1191,f738])).

fof(f738,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_102 ),
    inference(avatar_component_clause,[],[f736])).

fof(f1191,plain,
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
    | ~ spl6_34
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_108
    | ~ spl6_124 ),
    inference(forward_demodulation,[],[f1190,f781])).

fof(f1190,plain,
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
    | ~ spl6_34
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_124 ),
    inference(forward_demodulation,[],[f1189,f402])).

fof(f1189,plain,
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
    | ~ spl6_34
    | ~ spl6_50
    | ~ spl6_124 ),
    inference(forward_demodulation,[],[f1188,f286])).

fof(f1188,plain,
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
    | ~ spl6_50
    | ~ spl6_124 ),
    inference(forward_demodulation,[],[f1187,f359])).

fof(f1187,plain,
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
    | ~ spl6_50
    | ~ spl6_124 ),
    inference(forward_demodulation,[],[f1163,f406])).

fof(f1163,plain,
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
    | ~ spl6_124 ),
    inference(resolution,[],[f913,f99])).

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

fof(f913,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_124 ),
    inference(avatar_component_clause,[],[f911])).

fof(f1186,plain,
    ( spl6_15
    | spl6_1
    | ~ spl6_118
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
    | ~ spl6_34
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_102
    | ~ spl6_108
    | ~ spl6_124 ),
    inference(avatar_split_clause,[],[f1185,f911,f779,f736,f405,f401,f284,f128,f108,f118,f113,f133,f128,f148,f143,f138,f163,f158,f153,f769,f858,f103,f172])).

fof(f172,plain,
    ( spl6_15
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f1185,plain,
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
    | ~ spl6_34
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_102
    | ~ spl6_108
    | ~ spl6_124 ),
    inference(trivial_inequality_removal,[],[f1184])).

fof(f1184,plain,
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
    | ~ spl6_34
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_102
    | ~ spl6_108
    | ~ spl6_124 ),
    inference(forward_demodulation,[],[f1183,f738])).

fof(f1183,plain,
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
    | ~ spl6_34
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_108
    | ~ spl6_124 ),
    inference(forward_demodulation,[],[f1182,f781])).

fof(f1182,plain,
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
    | ~ spl6_34
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_124 ),
    inference(forward_demodulation,[],[f1181,f402])).

fof(f1181,plain,
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
    | ~ spl6_34
    | ~ spl6_50
    | ~ spl6_124 ),
    inference(forward_demodulation,[],[f1180,f286])).

fof(f1180,plain,
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
    | ~ spl6_50
    | ~ spl6_124 ),
    inference(forward_demodulation,[],[f1179,f359])).

fof(f1179,plain,
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
    | ~ spl6_50
    | ~ spl6_124 ),
    inference(forward_demodulation,[],[f1162,f406])).

fof(f1162,plain,
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
    | ~ spl6_124 ),
    inference(resolution,[],[f913,f100])).

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
    inference(cnf_transformation,[],[f29])).

fof(f914,plain,
    ( spl6_124
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_86 ),
    inference(avatar_split_clause,[],[f908,f614,f138,f143,f148,f911])).

fof(f614,plain,
    ( spl6_86
  <=> ! [X1] :
        ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f908,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_8
    | ~ spl6_86 ),
    inference(resolution,[],[f615,f140])).

fof(f140,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f615,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) )
    | ~ spl6_86 ),
    inference(avatar_component_clause,[],[f614])).

fof(f861,plain,
    ( spl6_118
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f855,f581,f138,f143,f148,f858])).

fof(f581,plain,
    ( spl6_80
  <=> ! [X1] :
        ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f855,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_8
    | ~ spl6_80 ),
    inference(resolution,[],[f582,f140])).

fof(f582,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) )
    | ~ spl6_80 ),
    inference(avatar_component_clause,[],[f581])).

fof(f782,plain,
    ( spl6_108
    | ~ spl6_65
    | ~ spl6_106 ),
    inference(avatar_split_clause,[],[f774,f762,f494,f779])).

fof(f494,plain,
    ( spl6_65
  <=> ! [X0] :
        ( ~ r1_xboole_0(sK3,X0)
        | k1_xboole_0 = k7_relat_1(sK5,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f762,plain,
    ( spl6_106
  <=> r1_xboole_0(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_106])])).

fof(f774,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_65
    | ~ spl6_106 ),
    inference(resolution,[],[f764,f495])).

fof(f495,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK3,X0)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl6_65 ),
    inference(avatar_component_clause,[],[f494])).

fof(f764,plain,
    ( r1_xboole_0(sK3,k1_xboole_0)
    | ~ spl6_106 ),
    inference(avatar_component_clause,[],[f762])).

fof(f772,plain,
    ( spl6_107
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f766,f546,f138,f143,f148,f769])).

fof(f546,plain,
    ( spl6_74
  <=> ! [X1] :
        ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f766,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_8
    | ~ spl6_74 ),
    inference(resolution,[],[f547,f140])).

fof(f547,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) )
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f546])).

fof(f765,plain,
    ( spl6_106
    | ~ spl6_26
    | ~ spl6_51
    | ~ spl6_98 ),
    inference(avatar_split_clause,[],[f760,f701,f410,f230,f762])).

fof(f230,plain,
    ( spl6_26
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f410,plain,
    ( spl6_51
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f701,plain,
    ( spl6_98
  <=> k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f760,plain,
    ( r1_xboole_0(sK3,k1_xboole_0)
    | ~ spl6_26
    | ~ spl6_51
    | ~ spl6_98 ),
    inference(trivial_inequality_removal,[],[f759])).

fof(f759,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK3,k1_xboole_0)
    | ~ spl6_26
    | ~ spl6_51
    | ~ spl6_98 ),
    inference(superposition,[],[f572,f703])).

fof(f703,plain,
    ( k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0)
    | ~ spl6_98 ),
    inference(avatar_component_clause,[],[f701])).

fof(f572,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k9_relat_1(sK5,X1)
        | r1_xboole_0(sK3,X1) )
    | ~ spl6_26
    | ~ spl6_51 ),
    inference(forward_demodulation,[],[f314,f412])).

fof(f412,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f410])).

fof(f314,plain,
    ( ! [X1] :
        ( r1_xboole_0(k1_relat_1(sK5),X1)
        | k1_xboole_0 != k9_relat_1(sK5,X1) )
    | ~ spl6_26 ),
    inference(resolution,[],[f78,f232])).

fof(f232,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f230])).

fof(f78,plain,(
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

fof(f739,plain,
    ( spl6_102
    | ~ spl6_59
    | ~ spl6_99 ),
    inference(avatar_split_clause,[],[f731,f708,f459,f736])).

fof(f459,plain,
    ( spl6_59
  <=> ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | k1_xboole_0 = k7_relat_1(sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f708,plain,
    ( spl6_99
  <=> r1_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).

fof(f731,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_59
    | ~ spl6_99 ),
    inference(resolution,[],[f710,f460])).

fof(f460,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f459])).

fof(f710,plain,
    ( r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl6_99 ),
    inference(avatar_component_clause,[],[f708])).

fof(f711,plain,
    ( spl6_99
    | ~ spl6_25
    | ~ spl6_48
    | ~ spl6_91 ),
    inference(avatar_split_clause,[],[f706,f652,f393,f225,f708])).

fof(f225,plain,
    ( spl6_25
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f393,plain,
    ( spl6_48
  <=> sK2 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f652,plain,
    ( spl6_91
  <=> k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f706,plain,
    ( r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl6_25
    | ~ spl6_48
    | ~ spl6_91 ),
    inference(trivial_inequality_removal,[],[f705])).

fof(f705,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl6_25
    | ~ spl6_48
    | ~ spl6_91 ),
    inference(superposition,[],[f537,f654])).

fof(f654,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0)
    | ~ spl6_91 ),
    inference(avatar_component_clause,[],[f652])).

fof(f537,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK4,X0)
        | r1_xboole_0(sK2,X0) )
    | ~ spl6_25
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f313,f395])).

fof(f395,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f393])).

fof(f313,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_relat_1(sK4),X0)
        | k1_xboole_0 != k9_relat_1(sK4,X0) )
    | ~ spl6_25 ),
    inference(resolution,[],[f78,f227])).

fof(f227,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f225])).

fof(f704,plain,
    ( spl6_98
    | ~ spl6_26
    | ~ spl6_30
    | ~ spl6_71
    | ~ spl6_72 ),
    inference(avatar_split_clause,[],[f699,f533,f526,f258,f230,f701])).

fof(f258,plain,
    ( spl6_30
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f526,plain,
    ( spl6_71
  <=> k1_xboole_0 = k7_relat_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f533,plain,
    ( spl6_72
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f699,plain,
    ( k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0)
    | ~ spl6_26
    | ~ spl6_30
    | ~ spl6_71
    | ~ spl6_72 ),
    inference(forward_demodulation,[],[f698,f260])).

fof(f260,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f258])).

fof(f698,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0)
    | ~ spl6_26
    | ~ spl6_71
    | ~ spl6_72 ),
    inference(forward_demodulation,[],[f687,f528])).

fof(f528,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl6_71 ),
    inference(avatar_component_clause,[],[f526])).

fof(f687,plain,
    ( k9_relat_1(sK5,k1_xboole_0) = k9_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0)
    | ~ spl6_26
    | ~ spl6_72 ),
    inference(resolution,[],[f364,f535])).

fof(f535,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl6_72 ),
    inference(avatar_component_clause,[],[f533])).

fof(f364,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k9_relat_1(k7_relat_1(sK5,X3),X2) = k9_relat_1(sK5,X2) )
    | ~ spl6_26 ),
    inference(resolution,[],[f72,f232])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f655,plain,
    ( spl6_91
    | ~ spl6_25
    | ~ spl6_30
    | ~ spl6_68
    | ~ spl6_69 ),
    inference(avatar_split_clause,[],[f650,f514,f507,f258,f225,f652])).

fof(f507,plain,
    ( spl6_68
  <=> k1_xboole_0 = k7_relat_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f514,plain,
    ( spl6_69
  <=> r1_tarski(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f650,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0)
    | ~ spl6_25
    | ~ spl6_30
    | ~ spl6_68
    | ~ spl6_69 ),
    inference(forward_demodulation,[],[f649,f260])).

fof(f649,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0)
    | ~ spl6_25
    | ~ spl6_68
    | ~ spl6_69 ),
    inference(forward_demodulation,[],[f642,f509])).

fof(f509,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f507])).

fof(f642,plain,
    ( k9_relat_1(sK4,k1_xboole_0) = k9_relat_1(k7_relat_1(sK4,sK3),k1_xboole_0)
    | ~ spl6_25
    | ~ spl6_69 ),
    inference(resolution,[],[f363,f516])).

fof(f516,plain,
    ( r1_tarski(k1_xboole_0,sK3)
    | ~ spl6_69 ),
    inference(avatar_component_clause,[],[f514])).

fof(f363,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k9_relat_1(sK4,X0) = k9_relat_1(k7_relat_1(sK4,X1),X0) )
    | ~ spl6_25 ),
    inference(resolution,[],[f72,f227])).

fof(f616,plain,
    ( ~ spl6_6
    | ~ spl6_12
    | spl6_7
    | ~ spl6_13
    | spl6_2
    | spl6_86
    | ~ spl6_11
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f607,f476,f153,f614,f108,f163,f133,f158,f128])).

fof(f476,plain,
    ( spl6_62
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f607,plain,
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
    | ~ spl6_62 ),
    inference(resolution,[],[f477,f155])).

fof(f155,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f153])).

fof(f477,plain,
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
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f476])).

fof(f583,plain,
    ( ~ spl6_6
    | ~ spl6_12
    | spl6_7
    | ~ spl6_13
    | spl6_2
    | spl6_80
    | ~ spl6_11
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f574,f441,f153,f581,f108,f163,f133,f158,f128])).

fof(f441,plain,
    ( spl6_56
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f574,plain,
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
    | ~ spl6_56 ),
    inference(resolution,[],[f442,f155])).

fof(f442,plain,
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
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f441])).

fof(f548,plain,
    ( ~ spl6_6
    | ~ spl6_12
    | spl6_7
    | ~ spl6_13
    | spl6_2
    | spl6_74
    | ~ spl6_11
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f539,f420,f153,f546,f108,f163,f133,f158,f128])).

fof(f420,plain,
    ( spl6_52
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f539,plain,
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
    | ~ spl6_52 ),
    inference(resolution,[],[f421,f155])).

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
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f420])).

fof(f536,plain,
    ( spl6_72
    | ~ spl6_18
    | ~ spl6_26
    | ~ spl6_71 ),
    inference(avatar_split_clause,[],[f531,f526,f230,f186,f533])).

fof(f186,plain,
    ( spl6_18
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f531,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl6_18
    | ~ spl6_26
    | ~ spl6_71 ),
    inference(forward_demodulation,[],[f530,f188])).

fof(f188,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f186])).

fof(f530,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK2)
    | ~ spl6_26
    | ~ spl6_71 ),
    inference(superposition,[],[f247,f528])).

fof(f247,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),X0)
    | ~ spl6_26 ),
    inference(resolution,[],[f232,f76])).

fof(f76,plain,(
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

fof(f529,plain,
    ( spl6_71
    | ~ spl6_33
    | ~ spl6_67 ),
    inference(avatar_split_clause,[],[f524,f502,f277,f526])).

fof(f277,plain,
    ( spl6_33
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f502,plain,
    ( spl6_67
  <=> ! [X2] :
        ( ~ r1_xboole_0(X2,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f524,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl6_33
    | ~ spl6_67 ),
    inference(resolution,[],[f503,f279])).

fof(f279,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f277])).

fof(f503,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X2) )
    | ~ spl6_67 ),
    inference(avatar_component_clause,[],[f502])).

fof(f517,plain,
    ( spl6_69
    | ~ spl6_18
    | ~ spl6_25
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f512,f507,f225,f186,f514])).

fof(f512,plain,
    ( r1_tarski(k1_xboole_0,sK3)
    | ~ spl6_18
    | ~ spl6_25
    | ~ spl6_68 ),
    inference(forward_demodulation,[],[f511,f188])).

fof(f511,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK3)
    | ~ spl6_25
    | ~ spl6_68 ),
    inference(superposition,[],[f239,f509])).

fof(f239,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0)
    | ~ spl6_25 ),
    inference(resolution,[],[f227,f76])).

fof(f510,plain,
    ( spl6_68
    | ~ spl6_33
    | ~ spl6_59 ),
    inference(avatar_split_clause,[],[f505,f459,f277,f507])).

fof(f505,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl6_33
    | ~ spl6_59 ),
    inference(resolution,[],[f460,f279])).

fof(f504,plain,
    ( ~ spl6_26
    | spl6_67
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f486,f410,f502,f230])).

fof(f486,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK3)
        | ~ v1_relat_1(sK5)
        | k1_xboole_0 = k7_relat_1(sK5,X2) )
    | ~ spl6_51 ),
    inference(superposition,[],[f71,f412])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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

fof(f496,plain,
    ( ~ spl6_26
    | spl6_65
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f484,f410,f494,f230])).

fof(f484,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK3,X0)
        | ~ v1_relat_1(sK5)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl6_51 ),
    inference(superposition,[],[f79,f412])).

fof(f79,plain,(
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

fof(f478,plain,
    ( spl6_1
    | spl6_4
    | spl6_62
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f470,f113,f476,f118,f103])).

fof(f470,plain,
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
    inference(resolution,[],[f93,f115])).

fof(f115,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f113])).

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

fof(f461,plain,
    ( ~ spl6_25
    | spl6_59
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f449,f393,f459,f225])).

fof(f449,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | ~ v1_relat_1(sK4)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl6_48 ),
    inference(superposition,[],[f79,f395])).

fof(f443,plain,
    ( spl6_1
    | spl6_4
    | spl6_56
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f435,f113,f441,f118,f103])).

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
    | ~ spl6_3 ),
    inference(resolution,[],[f92,f115])).

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
      | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f422,plain,
    ( spl6_1
    | spl6_4
    | spl6_52
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f414,f113,f420,f118,f103])).

fof(f414,plain,
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
    inference(resolution,[],[f91,f115])).

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
      | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f413,plain,
    ( ~ spl6_26
    | spl6_51
    | ~ spl6_32
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f408,f379,f271,f410,f230])).

fof(f271,plain,
    ( spl6_32
  <=> v4_relat_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f379,plain,
    ( spl6_45
  <=> v1_partfun1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f408,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl6_45 ),
    inference(resolution,[],[f381,f84])).

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
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f379])).

fof(f407,plain,
    ( spl6_50
    | ~ spl6_13
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f398,f153,f163,f405])).

fof(f398,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK5)
        | k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) )
    | ~ spl6_11 ),
    inference(resolution,[],[f90,f155])).

fof(f90,plain,(
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

fof(f403,plain,
    ( spl6_49
    | ~ spl6_10
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f397,f138,f148,f401])).

fof(f397,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) )
    | ~ spl6_8 ),
    inference(resolution,[],[f90,f140])).

fof(f396,plain,
    ( ~ spl6_25
    | spl6_48
    | ~ spl6_31
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f391,f374,f266,f393,f225])).

fof(f266,plain,
    ( spl6_31
  <=> v4_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f374,plain,
    ( spl6_44
  <=> v1_partfun1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f391,plain,
    ( ~ v4_relat_1(sK4,sK2)
    | sK2 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl6_44 ),
    inference(resolution,[],[f376,f84])).

fof(f376,plain,
    ( v1_partfun1(sK4,sK2)
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f374])).

fof(f382,plain,
    ( spl6_45
    | ~ spl6_12
    | ~ spl6_13
    | spl6_2
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f371,f153,f108,f163,f158,f379])).

fof(f371,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f75,f155])).

fof(f75,plain,(
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

fof(f377,plain,
    ( spl6_44
    | ~ spl6_9
    | ~ spl6_10
    | spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f370,f138,f108,f148,f143,f374])).

fof(f370,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f75,f140])).

fof(f287,plain,
    ( spl6_34
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f282,f277,f284])).

fof(f282,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl6_33 ),
    inference(resolution,[],[f279,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f86,f74])).

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

fof(f280,plain,
    ( spl6_4
    | spl6_33
    | spl6_7
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f275,f123,f133,f277,f118])).

fof(f123,plain,
    ( spl6_5
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f275,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f82,f125])).

fof(f125,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f123])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f274,plain,
    ( spl6_32
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f263,f153,f271])).

fof(f263,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f89,f155])).

fof(f89,plain,(
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

fof(f269,plain,
    ( spl6_31
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f262,f138,f266])).

fof(f262,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f89,f140])).

fof(f261,plain,
    ( spl6_30
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f256,f235,f186,f181,f258])).

fof(f181,plain,
    ( spl6_17
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f235,plain,
    ( spl6_27
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f256,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_27 ),
    inference(forward_demodulation,[],[f255,f183])).

fof(f183,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f181])).

fof(f255,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_18
    | ~ spl6_27 ),
    inference(forward_demodulation,[],[f253,f188])).

fof(f253,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl6_27 ),
    inference(resolution,[],[f237,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f237,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f235])).

fof(f238,plain,(
    spl6_27 ),
    inference(avatar_split_clause,[],[f223,f235])).

fof(f223,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f88,f66])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f88,plain,(
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

fof(f233,plain,
    ( spl6_26
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f222,f153,f230])).

fof(f222,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_11 ),
    inference(resolution,[],[f88,f155])).

fof(f228,plain,
    ( spl6_25
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f221,f138,f225])).

fof(f221,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_8 ),
    inference(resolution,[],[f88,f140])).

fof(f189,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f64,f186])).

fof(f64,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f184,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f65,f181])).

fof(f65,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f179,plain,
    ( ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f50,f176,f172,f168])).

fof(f50,plain,
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

fof(f166,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f51,f163])).

fof(f51,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f161,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f52,f158])).

fof(f52,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f156,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f53,f153])).

fof(f53,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f151,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f54,f148])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f146,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f55,f143])).

fof(f55,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f141,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f56,f138])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f136,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f57,f133])).

fof(f57,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f131,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f58,f128])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f126,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f59,f123])).

fof(f59,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f121,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f60,f118])).

fof(f60,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f116,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f61,f113])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f111,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f62,f108])).

fof(f62,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f106,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f63,f103])).

fof(f63,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:45:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (28851)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (28847)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (28867)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (28845)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (28846)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (28859)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (28871)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (28849)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (28848)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (28868)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (28869)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (28873)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (28844)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (28872)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (28861)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (28852)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (28863)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (28866)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (28865)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (28864)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (28853)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (28860)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (28858)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (28857)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (28856)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (28850)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  % (28855)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.58  % (28861)Refutation not found, incomplete strategy% (28861)------------------------------
% 0.21/0.58  % (28861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (28861)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (28861)Memory used [KB]: 10746
% 0.21/0.58  % (28861)Time elapsed: 0.166 s
% 0.21/0.58  % (28861)------------------------------
% 0.21/0.58  % (28861)------------------------------
% 0.21/0.58  % (28854)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.60  % (28870)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.76/0.60  % (28862)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.76/0.61  % (28866)Refutation not found, incomplete strategy% (28866)------------------------------
% 1.76/0.61  % (28866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.61  % (28866)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.61  
% 1.76/0.61  % (28866)Memory used [KB]: 11513
% 1.76/0.61  % (28866)Time elapsed: 0.156 s
% 1.76/0.61  % (28866)------------------------------
% 1.76/0.61  % (28866)------------------------------
% 2.01/0.64  % (28860)Refutation found. Thanks to Tanya!
% 2.01/0.64  % SZS status Theorem for theBenchmark
% 2.01/0.64  % SZS output start Proof for theBenchmark
% 2.01/0.64  fof(f1273,plain,(
% 2.01/0.64    $false),
% 2.01/0.64    inference(avatar_sat_refutation,[],[f106,f111,f116,f121,f126,f131,f136,f141,f146,f151,f156,f161,f166,f179,f184,f189,f228,f233,f238,f261,f269,f274,f280,f287,f377,f382,f396,f403,f407,f413,f422,f443,f461,f478,f496,f504,f510,f517,f529,f536,f548,f583,f616,f655,f704,f711,f739,f765,f772,f782,f861,f914,f1186,f1194,f1272])).
% 2.01/0.64  fof(f1272,plain,(
% 2.01/0.64    ~spl6_102 | ~spl6_6 | spl6_16 | ~spl6_34 | ~spl6_49 | ~spl6_50 | ~spl6_108),
% 2.01/0.64    inference(avatar_split_clause,[],[f1271,f779,f405,f401,f284,f176,f128,f736])).
% 2.01/0.64  fof(f736,plain,(
% 2.01/0.64    spl6_102 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).
% 2.01/0.64  fof(f128,plain,(
% 2.01/0.64    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.01/0.64  fof(f176,plain,(
% 2.01/0.64    spl6_16 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 2.01/0.64  fof(f284,plain,(
% 2.01/0.64    spl6_34 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 2.01/0.64  fof(f401,plain,(
% 2.01/0.64    spl6_49 <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 2.01/0.64  fof(f405,plain,(
% 2.01/0.64    spl6_50 <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 2.01/0.64  fof(f779,plain,(
% 2.01/0.64    spl6_108 <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_108])])).
% 2.01/0.64  fof(f1271,plain,(
% 2.01/0.64    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | (~spl6_6 | spl6_16 | ~spl6_34 | ~spl6_49 | ~spl6_50 | ~spl6_108)),
% 2.01/0.64    inference(forward_demodulation,[],[f1270,f781])).
% 2.01/0.64  fof(f781,plain,(
% 2.01/0.64    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | ~spl6_108),
% 2.01/0.64    inference(avatar_component_clause,[],[f779])).
% 2.01/0.64  fof(f1270,plain,(
% 2.01/0.64    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | (~spl6_6 | spl6_16 | ~spl6_34 | ~spl6_49 | ~spl6_50)),
% 2.01/0.64    inference(forward_demodulation,[],[f1269,f402])).
% 2.01/0.64  fof(f402,plain,(
% 2.01/0.64    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl6_49),
% 2.01/0.64    inference(avatar_component_clause,[],[f401])).
% 2.01/0.64  fof(f1269,plain,(
% 2.01/0.64    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (~spl6_6 | spl6_16 | ~spl6_34 | ~spl6_50)),
% 2.01/0.64    inference(forward_demodulation,[],[f1268,f286])).
% 2.01/0.64  fof(f286,plain,(
% 2.01/0.64    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl6_34),
% 2.01/0.64    inference(avatar_component_clause,[],[f284])).
% 2.01/0.64  fof(f1268,plain,(
% 2.01/0.64    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | (~spl6_6 | spl6_16 | ~spl6_50)),
% 2.01/0.64    inference(forward_demodulation,[],[f1267,f359])).
% 2.01/0.64  fof(f359,plain,(
% 2.01/0.64    ( ! [X1] : (k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))) ) | ~spl6_6),
% 2.01/0.64    inference(resolution,[],[f96,f130])).
% 2.01/0.64  fof(f130,plain,(
% 2.01/0.64    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl6_6),
% 2.01/0.64    inference(avatar_component_clause,[],[f128])).
% 2.01/0.64  fof(f96,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 2.01/0.64    inference(definition_unfolding,[],[f87,f74])).
% 2.01/0.64  fof(f74,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.01/0.64    inference(cnf_transformation,[],[f5])).
% 2.01/0.64  fof(f5,axiom,(
% 2.01/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.01/0.64  fof(f87,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f43])).
% 2.01/0.64  fof(f43,plain,(
% 2.01/0.64    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.01/0.64    inference(ennf_transformation,[],[f2])).
% 2.01/0.64  fof(f2,axiom,(
% 2.01/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.01/0.64  fof(f1267,plain,(
% 2.01/0.64    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (spl6_16 | ~spl6_50)),
% 2.01/0.64    inference(forward_demodulation,[],[f178,f406])).
% 2.01/0.64  fof(f406,plain,(
% 2.01/0.64    ( ! [X1] : (k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl6_50),
% 2.01/0.64    inference(avatar_component_clause,[],[f405])).
% 2.01/0.64  fof(f178,plain,(
% 2.01/0.64    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_16),
% 2.01/0.64    inference(avatar_component_clause,[],[f176])).
% 2.01/0.64  fof(f1194,plain,(
% 2.01/0.64    spl6_14 | spl6_1 | ~spl6_118 | ~spl6_107 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_6 | spl6_7 | ~spl6_3 | spl6_4 | spl6_2 | ~spl6_6 | ~spl6_34 | ~spl6_49 | ~spl6_50 | ~spl6_102 | ~spl6_108 | ~spl6_124),
% 2.01/0.64    inference(avatar_split_clause,[],[f1193,f911,f779,f736,f405,f401,f284,f128,f108,f118,f113,f133,f128,f148,f143,f138,f163,f158,f153,f769,f858,f103,f168])).
% 2.01/0.64  fof(f168,plain,(
% 2.01/0.64    spl6_14 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 2.01/0.64  fof(f103,plain,(
% 2.01/0.64    spl6_1 <=> v1_xboole_0(sK0)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.01/0.64  fof(f858,plain,(
% 2.01/0.64    spl6_118 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).
% 2.01/0.64  fof(f769,plain,(
% 2.01/0.64    spl6_107 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).
% 2.01/0.64  fof(f153,plain,(
% 2.01/0.64    spl6_11 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 2.01/0.64  fof(f158,plain,(
% 2.01/0.64    spl6_12 <=> v1_funct_2(sK5,sK3,sK1)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 2.01/0.64  fof(f163,plain,(
% 2.01/0.64    spl6_13 <=> v1_funct_1(sK5)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 2.01/0.64  fof(f138,plain,(
% 2.01/0.64    spl6_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.01/0.64  fof(f143,plain,(
% 2.01/0.64    spl6_9 <=> v1_funct_2(sK4,sK2,sK1)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 2.01/0.64  fof(f148,plain,(
% 2.01/0.64    spl6_10 <=> v1_funct_1(sK4)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.01/0.64  fof(f133,plain,(
% 2.01/0.64    spl6_7 <=> v1_xboole_0(sK3)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.01/0.64  fof(f113,plain,(
% 2.01/0.64    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.01/0.64  fof(f118,plain,(
% 2.01/0.64    spl6_4 <=> v1_xboole_0(sK2)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.01/0.64  fof(f108,plain,(
% 2.01/0.64    spl6_2 <=> v1_xboole_0(sK1)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.01/0.64  fof(f911,plain,(
% 2.01/0.64    spl6_124 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_124])])).
% 2.01/0.64  fof(f1193,plain,(
% 2.01/0.64    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_34 | ~spl6_49 | ~spl6_50 | ~spl6_102 | ~spl6_108 | ~spl6_124)),
% 2.01/0.64    inference(trivial_inequality_removal,[],[f1192])).
% 2.01/0.64  fof(f1192,plain,(
% 2.01/0.64    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_34 | ~spl6_49 | ~spl6_50 | ~spl6_102 | ~spl6_108 | ~spl6_124)),
% 2.01/0.64    inference(forward_demodulation,[],[f1191,f738])).
% 2.01/0.64  fof(f738,plain,(
% 2.01/0.64    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl6_102),
% 2.01/0.64    inference(avatar_component_clause,[],[f736])).
% 2.01/0.64  fof(f1191,plain,(
% 2.01/0.64    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_34 | ~spl6_49 | ~spl6_50 | ~spl6_108 | ~spl6_124)),
% 2.01/0.64    inference(forward_demodulation,[],[f1190,f781])).
% 2.01/0.64  fof(f1190,plain,(
% 2.01/0.64    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_34 | ~spl6_49 | ~spl6_50 | ~spl6_124)),
% 2.01/0.64    inference(forward_demodulation,[],[f1189,f402])).
% 2.01/0.64  fof(f1189,plain,(
% 2.01/0.64    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_34 | ~spl6_50 | ~spl6_124)),
% 2.01/0.64    inference(forward_demodulation,[],[f1188,f286])).
% 2.01/0.64  fof(f1188,plain,(
% 2.01/0.64    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_50 | ~spl6_124)),
% 2.01/0.64    inference(forward_demodulation,[],[f1187,f359])).
% 2.01/0.64  fof(f1187,plain,(
% 2.01/0.64    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_50 | ~spl6_124)),
% 2.01/0.64    inference(forward_demodulation,[],[f1163,f406])).
% 2.01/0.64  fof(f1163,plain,(
% 2.01/0.64    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~spl6_124),
% 2.01/0.64    inference(resolution,[],[f913,f99])).
% 2.01/0.64  fof(f99,plain,(
% 2.01/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 2.01/0.64    inference(equality_resolution,[],[f68])).
% 2.01/0.64  fof(f68,plain,(
% 2.01/0.64    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 2.01/0.64    inference(cnf_transformation,[],[f29])).
% 2.01/0.64  fof(f29,plain,(
% 2.01/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.01/0.64    inference(flattening,[],[f28])).
% 2.01/0.64  fof(f28,plain,(
% 2.01/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.01/0.64    inference(ennf_transformation,[],[f20])).
% 2.01/0.64  fof(f20,axiom,(
% 2.01/0.64    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 2.01/0.64  fof(f913,plain,(
% 2.01/0.64    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl6_124),
% 2.01/0.64    inference(avatar_component_clause,[],[f911])).
% 2.01/0.64  fof(f1186,plain,(
% 2.01/0.64    spl6_15 | spl6_1 | ~spl6_118 | ~spl6_107 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_6 | spl6_7 | ~spl6_3 | spl6_4 | spl6_2 | ~spl6_6 | ~spl6_34 | ~spl6_49 | ~spl6_50 | ~spl6_102 | ~spl6_108 | ~spl6_124),
% 2.01/0.64    inference(avatar_split_clause,[],[f1185,f911,f779,f736,f405,f401,f284,f128,f108,f118,f113,f133,f128,f148,f143,f138,f163,f158,f153,f769,f858,f103,f172])).
% 2.01/0.64  fof(f172,plain,(
% 2.01/0.64    spl6_15 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 2.01/0.64  fof(f1185,plain,(
% 2.01/0.64    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_34 | ~spl6_49 | ~spl6_50 | ~spl6_102 | ~spl6_108 | ~spl6_124)),
% 2.01/0.64    inference(trivial_inequality_removal,[],[f1184])).
% 2.01/0.64  fof(f1184,plain,(
% 2.01/0.64    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_34 | ~spl6_49 | ~spl6_50 | ~spl6_102 | ~spl6_108 | ~spl6_124)),
% 2.01/0.64    inference(forward_demodulation,[],[f1183,f738])).
% 2.01/0.64  fof(f1183,plain,(
% 2.01/0.64    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_34 | ~spl6_49 | ~spl6_50 | ~spl6_108 | ~spl6_124)),
% 2.01/0.64    inference(forward_demodulation,[],[f1182,f781])).
% 2.01/0.64  fof(f1182,plain,(
% 2.01/0.64    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_34 | ~spl6_49 | ~spl6_50 | ~spl6_124)),
% 2.01/0.64    inference(forward_demodulation,[],[f1181,f402])).
% 2.01/0.64  fof(f1181,plain,(
% 2.01/0.64    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_34 | ~spl6_50 | ~spl6_124)),
% 2.01/0.64    inference(forward_demodulation,[],[f1180,f286])).
% 2.01/0.64  fof(f1180,plain,(
% 2.01/0.64    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_50 | ~spl6_124)),
% 2.01/0.64    inference(forward_demodulation,[],[f1179,f359])).
% 2.01/0.64  fof(f1179,plain,(
% 2.01/0.64    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_50 | ~spl6_124)),
% 2.01/0.64    inference(forward_demodulation,[],[f1162,f406])).
% 2.01/0.64  fof(f1162,plain,(
% 2.01/0.64    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~spl6_124),
% 2.01/0.64    inference(resolution,[],[f913,f100])).
% 2.01/0.64  fof(f100,plain,(
% 2.01/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 2.01/0.64    inference(equality_resolution,[],[f67])).
% 2.01/0.64  fof(f67,plain,(
% 2.01/0.64    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 2.01/0.64    inference(cnf_transformation,[],[f29])).
% 2.01/0.64  fof(f914,plain,(
% 2.01/0.64    spl6_124 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_86),
% 2.01/0.64    inference(avatar_split_clause,[],[f908,f614,f138,f143,f148,f911])).
% 2.01/0.64  fof(f614,plain,(
% 2.01/0.64    spl6_86 <=> ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).
% 2.01/0.64  fof(f908,plain,(
% 2.01/0.64    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_8 | ~spl6_86)),
% 2.01/0.64    inference(resolution,[],[f615,f140])).
% 2.01/0.64  fof(f140,plain,(
% 2.01/0.64    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl6_8),
% 2.01/0.64    inference(avatar_component_clause,[],[f138])).
% 2.01/0.64  fof(f615,plain,(
% 2.01/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))) ) | ~spl6_86),
% 2.01/0.64    inference(avatar_component_clause,[],[f614])).
% 2.01/0.64  fof(f861,plain,(
% 2.01/0.64    spl6_118 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_80),
% 2.01/0.64    inference(avatar_split_clause,[],[f855,f581,f138,f143,f148,f858])).
% 2.01/0.64  fof(f581,plain,(
% 2.01/0.64    spl6_80 <=> ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).
% 2.01/0.64  fof(f855,plain,(
% 2.01/0.64    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_8 | ~spl6_80)),
% 2.01/0.64    inference(resolution,[],[f582,f140])).
% 2.01/0.64  fof(f582,plain,(
% 2.01/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)) ) | ~spl6_80),
% 2.01/0.64    inference(avatar_component_clause,[],[f581])).
% 2.01/0.64  fof(f782,plain,(
% 2.01/0.64    spl6_108 | ~spl6_65 | ~spl6_106),
% 2.01/0.64    inference(avatar_split_clause,[],[f774,f762,f494,f779])).
% 2.01/0.64  fof(f494,plain,(
% 2.01/0.64    spl6_65 <=> ! [X0] : (~r1_xboole_0(sK3,X0) | k1_xboole_0 = k7_relat_1(sK5,X0))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 2.01/0.64  fof(f762,plain,(
% 2.01/0.64    spl6_106 <=> r1_xboole_0(sK3,k1_xboole_0)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_106])])).
% 2.01/0.64  fof(f774,plain,(
% 2.01/0.64    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | (~spl6_65 | ~spl6_106)),
% 2.01/0.64    inference(resolution,[],[f764,f495])).
% 2.01/0.64  fof(f495,plain,(
% 2.01/0.64    ( ! [X0] : (~r1_xboole_0(sK3,X0) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl6_65),
% 2.01/0.64    inference(avatar_component_clause,[],[f494])).
% 2.01/0.64  fof(f764,plain,(
% 2.01/0.64    r1_xboole_0(sK3,k1_xboole_0) | ~spl6_106),
% 2.01/0.64    inference(avatar_component_clause,[],[f762])).
% 2.01/0.64  fof(f772,plain,(
% 2.01/0.64    spl6_107 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_74),
% 2.01/0.64    inference(avatar_split_clause,[],[f766,f546,f138,f143,f148,f769])).
% 2.01/0.64  fof(f546,plain,(
% 2.01/0.64    spl6_74 <=> ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 2.01/0.64  fof(f766,plain,(
% 2.01/0.64    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_8 | ~spl6_74)),
% 2.01/0.64    inference(resolution,[],[f547,f140])).
% 2.01/0.64  fof(f547,plain,(
% 2.01/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))) ) | ~spl6_74),
% 2.01/0.64    inference(avatar_component_clause,[],[f546])).
% 2.01/0.64  fof(f765,plain,(
% 2.01/0.64    spl6_106 | ~spl6_26 | ~spl6_51 | ~spl6_98),
% 2.01/0.64    inference(avatar_split_clause,[],[f760,f701,f410,f230,f762])).
% 2.01/0.64  fof(f230,plain,(
% 2.01/0.64    spl6_26 <=> v1_relat_1(sK5)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 2.01/0.64  fof(f410,plain,(
% 2.01/0.64    spl6_51 <=> sK3 = k1_relat_1(sK5)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 2.01/0.64  fof(f701,plain,(
% 2.01/0.64    spl6_98 <=> k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).
% 2.01/0.64  fof(f760,plain,(
% 2.01/0.64    r1_xboole_0(sK3,k1_xboole_0) | (~spl6_26 | ~spl6_51 | ~spl6_98)),
% 2.01/0.64    inference(trivial_inequality_removal,[],[f759])).
% 2.01/0.64  fof(f759,plain,(
% 2.01/0.64    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK3,k1_xboole_0) | (~spl6_26 | ~spl6_51 | ~spl6_98)),
% 2.01/0.64    inference(superposition,[],[f572,f703])).
% 2.01/0.64  fof(f703,plain,(
% 2.01/0.64    k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0) | ~spl6_98),
% 2.01/0.64    inference(avatar_component_clause,[],[f701])).
% 2.01/0.64  fof(f572,plain,(
% 2.01/0.64    ( ! [X1] : (k1_xboole_0 != k9_relat_1(sK5,X1) | r1_xboole_0(sK3,X1)) ) | (~spl6_26 | ~spl6_51)),
% 2.01/0.64    inference(forward_demodulation,[],[f314,f412])).
% 2.01/0.64  fof(f412,plain,(
% 2.01/0.64    sK3 = k1_relat_1(sK5) | ~spl6_51),
% 2.01/0.64    inference(avatar_component_clause,[],[f410])).
% 2.01/0.64  fof(f314,plain,(
% 2.01/0.64    ( ! [X1] : (r1_xboole_0(k1_relat_1(sK5),X1) | k1_xboole_0 != k9_relat_1(sK5,X1)) ) | ~spl6_26),
% 2.01/0.64    inference(resolution,[],[f78,f232])).
% 2.01/0.64  fof(f232,plain,(
% 2.01/0.64    v1_relat_1(sK5) | ~spl6_26),
% 2.01/0.64    inference(avatar_component_clause,[],[f230])).
% 2.01/0.64  fof(f78,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f37])).
% 2.01/0.64  fof(f37,plain,(
% 2.01/0.64    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.01/0.64    inference(ennf_transformation,[],[f8])).
% 2.01/0.64  fof(f8,axiom,(
% 2.01/0.64    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 2.01/0.64  fof(f739,plain,(
% 2.01/0.64    spl6_102 | ~spl6_59 | ~spl6_99),
% 2.01/0.64    inference(avatar_split_clause,[],[f731,f708,f459,f736])).
% 2.01/0.64  fof(f459,plain,(
% 2.01/0.64    spl6_59 <=> ! [X0] : (~r1_xboole_0(sK2,X0) | k1_xboole_0 = k7_relat_1(sK4,X0))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 2.01/0.64  fof(f708,plain,(
% 2.01/0.64    spl6_99 <=> r1_xboole_0(sK2,k1_xboole_0)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).
% 2.01/0.64  fof(f731,plain,(
% 2.01/0.64    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | (~spl6_59 | ~spl6_99)),
% 2.01/0.64    inference(resolution,[],[f710,f460])).
% 2.01/0.64  fof(f460,plain,(
% 2.01/0.64    ( ! [X0] : (~r1_xboole_0(sK2,X0) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl6_59),
% 2.01/0.64    inference(avatar_component_clause,[],[f459])).
% 2.01/0.64  fof(f710,plain,(
% 2.01/0.64    r1_xboole_0(sK2,k1_xboole_0) | ~spl6_99),
% 2.01/0.64    inference(avatar_component_clause,[],[f708])).
% 2.01/0.64  fof(f711,plain,(
% 2.01/0.64    spl6_99 | ~spl6_25 | ~spl6_48 | ~spl6_91),
% 2.01/0.64    inference(avatar_split_clause,[],[f706,f652,f393,f225,f708])).
% 2.01/0.64  fof(f225,plain,(
% 2.01/0.64    spl6_25 <=> v1_relat_1(sK4)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 2.01/0.64  fof(f393,plain,(
% 2.01/0.64    spl6_48 <=> sK2 = k1_relat_1(sK4)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 2.01/0.64  fof(f652,plain,(
% 2.01/0.64    spl6_91 <=> k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).
% 2.01/0.64  fof(f706,plain,(
% 2.01/0.64    r1_xboole_0(sK2,k1_xboole_0) | (~spl6_25 | ~spl6_48 | ~spl6_91)),
% 2.01/0.64    inference(trivial_inequality_removal,[],[f705])).
% 2.01/0.64  fof(f705,plain,(
% 2.01/0.64    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK2,k1_xboole_0) | (~spl6_25 | ~spl6_48 | ~spl6_91)),
% 2.01/0.64    inference(superposition,[],[f537,f654])).
% 2.01/0.64  fof(f654,plain,(
% 2.01/0.64    k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0) | ~spl6_91),
% 2.01/0.64    inference(avatar_component_clause,[],[f652])).
% 2.01/0.64  fof(f537,plain,(
% 2.01/0.64    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK4,X0) | r1_xboole_0(sK2,X0)) ) | (~spl6_25 | ~spl6_48)),
% 2.01/0.64    inference(forward_demodulation,[],[f313,f395])).
% 2.01/0.64  fof(f395,plain,(
% 2.01/0.64    sK2 = k1_relat_1(sK4) | ~spl6_48),
% 2.01/0.64    inference(avatar_component_clause,[],[f393])).
% 2.01/0.64  fof(f313,plain,(
% 2.01/0.64    ( ! [X0] : (r1_xboole_0(k1_relat_1(sK4),X0) | k1_xboole_0 != k9_relat_1(sK4,X0)) ) | ~spl6_25),
% 2.01/0.64    inference(resolution,[],[f78,f227])).
% 2.01/0.64  fof(f227,plain,(
% 2.01/0.64    v1_relat_1(sK4) | ~spl6_25),
% 2.01/0.64    inference(avatar_component_clause,[],[f225])).
% 2.01/0.64  fof(f704,plain,(
% 2.01/0.64    spl6_98 | ~spl6_26 | ~spl6_30 | ~spl6_71 | ~spl6_72),
% 2.01/0.64    inference(avatar_split_clause,[],[f699,f533,f526,f258,f230,f701])).
% 2.01/0.64  fof(f258,plain,(
% 2.01/0.64    spl6_30 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 2.01/0.64  fof(f526,plain,(
% 2.01/0.64    spl6_71 <=> k1_xboole_0 = k7_relat_1(sK5,sK2)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).
% 2.01/0.64  fof(f533,plain,(
% 2.01/0.64    spl6_72 <=> r1_tarski(k1_xboole_0,sK2)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).
% 2.01/0.64  fof(f699,plain,(
% 2.01/0.64    k1_xboole_0 = k9_relat_1(sK5,k1_xboole_0) | (~spl6_26 | ~spl6_30 | ~spl6_71 | ~spl6_72)),
% 2.01/0.64    inference(forward_demodulation,[],[f698,f260])).
% 2.01/0.64  fof(f260,plain,(
% 2.01/0.64    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | ~spl6_30),
% 2.01/0.64    inference(avatar_component_clause,[],[f258])).
% 2.01/0.64  fof(f698,plain,(
% 2.01/0.64    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0) | (~spl6_26 | ~spl6_71 | ~spl6_72)),
% 2.01/0.64    inference(forward_demodulation,[],[f687,f528])).
% 2.01/0.64  fof(f528,plain,(
% 2.01/0.64    k1_xboole_0 = k7_relat_1(sK5,sK2) | ~spl6_71),
% 2.01/0.64    inference(avatar_component_clause,[],[f526])).
% 2.01/0.64  fof(f687,plain,(
% 2.01/0.64    k9_relat_1(sK5,k1_xboole_0) = k9_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0) | (~spl6_26 | ~spl6_72)),
% 2.01/0.64    inference(resolution,[],[f364,f535])).
% 2.01/0.64  fof(f535,plain,(
% 2.01/0.64    r1_tarski(k1_xboole_0,sK2) | ~spl6_72),
% 2.01/0.64    inference(avatar_component_clause,[],[f533])).
% 2.01/0.64  fof(f364,plain,(
% 2.01/0.64    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k9_relat_1(k7_relat_1(sK5,X3),X2) = k9_relat_1(sK5,X2)) ) | ~spl6_26),
% 2.01/0.64    inference(resolution,[],[f72,f232])).
% 2.01/0.64  fof(f72,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f32])).
% 2.01/0.64  fof(f32,plain,(
% 2.01/0.64    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 2.01/0.64    inference(ennf_transformation,[],[f9])).
% 2.01/0.64  fof(f9,axiom,(
% 2.01/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 2.01/0.64  fof(f655,plain,(
% 2.01/0.64    spl6_91 | ~spl6_25 | ~spl6_30 | ~spl6_68 | ~spl6_69),
% 2.01/0.64    inference(avatar_split_clause,[],[f650,f514,f507,f258,f225,f652])).
% 2.01/0.64  fof(f507,plain,(
% 2.01/0.64    spl6_68 <=> k1_xboole_0 = k7_relat_1(sK4,sK3)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 2.01/0.64  fof(f514,plain,(
% 2.01/0.64    spl6_69 <=> r1_tarski(k1_xboole_0,sK3)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).
% 2.01/0.64  fof(f650,plain,(
% 2.01/0.64    k1_xboole_0 = k9_relat_1(sK4,k1_xboole_0) | (~spl6_25 | ~spl6_30 | ~spl6_68 | ~spl6_69)),
% 2.01/0.64    inference(forward_demodulation,[],[f649,f260])).
% 2.01/0.64  fof(f649,plain,(
% 2.01/0.64    k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0) | (~spl6_25 | ~spl6_68 | ~spl6_69)),
% 2.01/0.64    inference(forward_demodulation,[],[f642,f509])).
% 2.01/0.64  fof(f509,plain,(
% 2.01/0.64    k1_xboole_0 = k7_relat_1(sK4,sK3) | ~spl6_68),
% 2.01/0.64    inference(avatar_component_clause,[],[f507])).
% 2.01/0.64  fof(f642,plain,(
% 2.01/0.64    k9_relat_1(sK4,k1_xboole_0) = k9_relat_1(k7_relat_1(sK4,sK3),k1_xboole_0) | (~spl6_25 | ~spl6_69)),
% 2.01/0.64    inference(resolution,[],[f363,f516])).
% 2.01/0.64  fof(f516,plain,(
% 2.01/0.64    r1_tarski(k1_xboole_0,sK3) | ~spl6_69),
% 2.01/0.64    inference(avatar_component_clause,[],[f514])).
% 2.01/0.64  fof(f363,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k9_relat_1(sK4,X0) = k9_relat_1(k7_relat_1(sK4,X1),X0)) ) | ~spl6_25),
% 2.01/0.64    inference(resolution,[],[f72,f227])).
% 2.01/0.64  fof(f616,plain,(
% 2.01/0.64    ~spl6_6 | ~spl6_12 | spl6_7 | ~spl6_13 | spl6_2 | spl6_86 | ~spl6_11 | ~spl6_62),
% 2.01/0.64    inference(avatar_split_clause,[],[f607,f476,f153,f614,f108,f163,f133,f158,f128])).
% 2.01/0.64  fof(f476,plain,(
% 2.01/0.64    spl6_62 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 2.01/0.64  fof(f607,plain,(
% 2.01/0.64    ( ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl6_11 | ~spl6_62)),
% 2.01/0.64    inference(resolution,[],[f477,f155])).
% 2.01/0.64  fof(f155,plain,(
% 2.01/0.64    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl6_11),
% 2.01/0.64    inference(avatar_component_clause,[],[f153])).
% 2.01/0.64  fof(f477,plain,(
% 2.01/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl6_62),
% 2.01/0.64    inference(avatar_component_clause,[],[f476])).
% 2.01/0.64  fof(f583,plain,(
% 2.01/0.64    ~spl6_6 | ~spl6_12 | spl6_7 | ~spl6_13 | spl6_2 | spl6_80 | ~spl6_11 | ~spl6_56),
% 2.01/0.64    inference(avatar_split_clause,[],[f574,f441,f153,f581,f108,f163,f133,f158,f128])).
% 2.01/0.64  fof(f441,plain,(
% 2.01/0.64    spl6_56 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).
% 2.01/0.64  fof(f574,plain,(
% 2.01/0.64    ( ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl6_11 | ~spl6_56)),
% 2.01/0.64    inference(resolution,[],[f442,f155])).
% 2.01/0.64  fof(f442,plain,(
% 2.01/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl6_56),
% 2.01/0.64    inference(avatar_component_clause,[],[f441])).
% 2.01/0.64  fof(f548,plain,(
% 2.01/0.64    ~spl6_6 | ~spl6_12 | spl6_7 | ~spl6_13 | spl6_2 | spl6_74 | ~spl6_11 | ~spl6_52),
% 2.01/0.64    inference(avatar_split_clause,[],[f539,f420,f153,f546,f108,f163,f133,f158,f128])).
% 2.01/0.64  fof(f420,plain,(
% 2.01/0.64    spl6_52 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 2.01/0.64  fof(f539,plain,(
% 2.01/0.64    ( ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl6_11 | ~spl6_52)),
% 2.01/0.64    inference(resolution,[],[f421,f155])).
% 2.01/0.64  fof(f421,plain,(
% 2.01/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl6_52),
% 2.01/0.64    inference(avatar_component_clause,[],[f420])).
% 2.01/0.64  fof(f536,plain,(
% 2.01/0.64    spl6_72 | ~spl6_18 | ~spl6_26 | ~spl6_71),
% 2.01/0.64    inference(avatar_split_clause,[],[f531,f526,f230,f186,f533])).
% 2.01/0.64  fof(f186,plain,(
% 2.01/0.64    spl6_18 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 2.01/0.64  fof(f531,plain,(
% 2.01/0.64    r1_tarski(k1_xboole_0,sK2) | (~spl6_18 | ~spl6_26 | ~spl6_71)),
% 2.01/0.64    inference(forward_demodulation,[],[f530,f188])).
% 2.01/0.64  fof(f188,plain,(
% 2.01/0.64    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_18),
% 2.01/0.64    inference(avatar_component_clause,[],[f186])).
% 2.01/0.64  fof(f530,plain,(
% 2.01/0.64    r1_tarski(k1_relat_1(k1_xboole_0),sK2) | (~spl6_26 | ~spl6_71)),
% 2.01/0.64    inference(superposition,[],[f247,f528])).
% 2.01/0.64  fof(f247,plain,(
% 2.01/0.64    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),X0)) ) | ~spl6_26),
% 2.01/0.64    inference(resolution,[],[f232,f76])).
% 2.01/0.64  fof(f76,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f36])).
% 2.01/0.64  fof(f36,plain,(
% 2.01/0.64    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.01/0.64    inference(ennf_transformation,[],[f12])).
% 2.01/0.64  fof(f12,axiom,(
% 2.01/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 2.01/0.64  fof(f529,plain,(
% 2.01/0.64    spl6_71 | ~spl6_33 | ~spl6_67),
% 2.01/0.64    inference(avatar_split_clause,[],[f524,f502,f277,f526])).
% 2.01/0.64  fof(f277,plain,(
% 2.01/0.64    spl6_33 <=> r1_xboole_0(sK2,sK3)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 2.01/0.64  fof(f502,plain,(
% 2.01/0.64    spl6_67 <=> ! [X2] : (~r1_xboole_0(X2,sK3) | k1_xboole_0 = k7_relat_1(sK5,X2))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).
% 2.01/0.64  fof(f524,plain,(
% 2.01/0.64    k1_xboole_0 = k7_relat_1(sK5,sK2) | (~spl6_33 | ~spl6_67)),
% 2.01/0.64    inference(resolution,[],[f503,f279])).
% 2.01/0.64  fof(f279,plain,(
% 2.01/0.64    r1_xboole_0(sK2,sK3) | ~spl6_33),
% 2.01/0.64    inference(avatar_component_clause,[],[f277])).
% 2.01/0.64  fof(f503,plain,(
% 2.01/0.64    ( ! [X2] : (~r1_xboole_0(X2,sK3) | k1_xboole_0 = k7_relat_1(sK5,X2)) ) | ~spl6_67),
% 2.01/0.64    inference(avatar_component_clause,[],[f502])).
% 2.01/0.64  fof(f517,plain,(
% 2.01/0.64    spl6_69 | ~spl6_18 | ~spl6_25 | ~spl6_68),
% 2.01/0.64    inference(avatar_split_clause,[],[f512,f507,f225,f186,f514])).
% 2.01/0.64  fof(f512,plain,(
% 2.01/0.64    r1_tarski(k1_xboole_0,sK3) | (~spl6_18 | ~spl6_25 | ~spl6_68)),
% 2.01/0.64    inference(forward_demodulation,[],[f511,f188])).
% 2.01/0.64  fof(f511,plain,(
% 2.01/0.64    r1_tarski(k1_relat_1(k1_xboole_0),sK3) | (~spl6_25 | ~spl6_68)),
% 2.01/0.64    inference(superposition,[],[f239,f509])).
% 2.01/0.64  fof(f239,plain,(
% 2.01/0.64    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0)) ) | ~spl6_25),
% 2.01/0.64    inference(resolution,[],[f227,f76])).
% 2.01/0.64  fof(f510,plain,(
% 2.01/0.64    spl6_68 | ~spl6_33 | ~spl6_59),
% 2.01/0.64    inference(avatar_split_clause,[],[f505,f459,f277,f507])).
% 2.01/0.64  fof(f505,plain,(
% 2.01/0.64    k1_xboole_0 = k7_relat_1(sK4,sK3) | (~spl6_33 | ~spl6_59)),
% 2.01/0.64    inference(resolution,[],[f460,f279])).
% 2.01/0.64  fof(f504,plain,(
% 2.01/0.64    ~spl6_26 | spl6_67 | ~spl6_51),
% 2.01/0.64    inference(avatar_split_clause,[],[f486,f410,f502,f230])).
% 2.01/0.64  fof(f486,plain,(
% 2.01/0.64    ( ! [X2] : (~r1_xboole_0(X2,sK3) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X2)) ) | ~spl6_51),
% 2.01/0.64    inference(superposition,[],[f71,f412])).
% 2.01/0.64  fof(f71,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f31])).
% 2.01/0.64  fof(f31,plain,(
% 2.01/0.64    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.01/0.64    inference(ennf_transformation,[],[f10])).
% 2.01/0.64  fof(f10,axiom,(
% 2.01/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 2.01/0.64  fof(f496,plain,(
% 2.01/0.64    ~spl6_26 | spl6_65 | ~spl6_51),
% 2.01/0.64    inference(avatar_split_clause,[],[f484,f410,f494,f230])).
% 2.01/0.64  fof(f484,plain,(
% 2.01/0.64    ( ! [X0] : (~r1_xboole_0(sK3,X0) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl6_51),
% 2.01/0.64    inference(superposition,[],[f79,f412])).
% 2.01/0.64  fof(f79,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f38])).
% 2.01/0.64  fof(f38,plain,(
% 2.01/0.64    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.01/0.64    inference(ennf_transformation,[],[f13])).
% 2.01/0.64  fof(f13,axiom,(
% 2.01/0.64    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 2.01/0.64  fof(f478,plain,(
% 2.01/0.64    spl6_1 | spl6_4 | spl6_62 | ~spl6_3),
% 2.01/0.64    inference(avatar_split_clause,[],[f470,f113,f476,f118,f103])).
% 2.01/0.64  fof(f470,plain,(
% 2.01/0.64    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0)))) ) | ~spl6_3),
% 2.01/0.64    inference(resolution,[],[f93,f115])).
% 2.01/0.64  fof(f115,plain,(
% 2.01/0.64    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl6_3),
% 2.01/0.64    inference(avatar_component_clause,[],[f113])).
% 2.01/0.64  fof(f93,plain,(
% 2.01/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 2.01/0.64    inference(cnf_transformation,[],[f49])).
% 2.01/0.64  fof(f49,plain,(
% 2.01/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.01/0.64    inference(flattening,[],[f48])).
% 2.01/0.64  fof(f48,plain,(
% 2.01/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.01/0.64    inference(ennf_transformation,[],[f21])).
% 2.01/0.64  fof(f21,axiom,(
% 2.01/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 2.01/0.64  fof(f461,plain,(
% 2.01/0.64    ~spl6_25 | spl6_59 | ~spl6_48),
% 2.01/0.64    inference(avatar_split_clause,[],[f449,f393,f459,f225])).
% 2.01/0.64  fof(f449,plain,(
% 2.01/0.64    ( ! [X0] : (~r1_xboole_0(sK2,X0) | ~v1_relat_1(sK4) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl6_48),
% 2.01/0.64    inference(superposition,[],[f79,f395])).
% 2.01/0.64  fof(f443,plain,(
% 2.01/0.64    spl6_1 | spl6_4 | spl6_56 | ~spl6_3),
% 2.01/0.64    inference(avatar_split_clause,[],[f435,f113,f441,f118,f103])).
% 2.01/0.64  fof(f435,plain,(
% 2.01/0.64    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0)) ) | ~spl6_3),
% 2.01/0.64    inference(resolution,[],[f92,f115])).
% 2.01/0.64  fof(f92,plain,(
% 2.01/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f49])).
% 2.01/0.64  fof(f422,plain,(
% 2.01/0.64    spl6_1 | spl6_4 | spl6_52 | ~spl6_3),
% 2.01/0.64    inference(avatar_split_clause,[],[f414,f113,f420,f118,f103])).
% 2.01/0.64  fof(f414,plain,(
% 2.01/0.64    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3))) ) | ~spl6_3),
% 2.01/0.64    inference(resolution,[],[f91,f115])).
% 2.01/0.64  fof(f91,plain,(
% 2.01/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 2.01/0.64    inference(cnf_transformation,[],[f49])).
% 2.01/0.64  fof(f413,plain,(
% 2.01/0.64    ~spl6_26 | spl6_51 | ~spl6_32 | ~spl6_45),
% 2.01/0.64    inference(avatar_split_clause,[],[f408,f379,f271,f410,f230])).
% 2.01/0.64  fof(f271,plain,(
% 2.01/0.64    spl6_32 <=> v4_relat_1(sK5,sK3)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 2.01/0.64  fof(f379,plain,(
% 2.01/0.64    spl6_45 <=> v1_partfun1(sK5,sK3)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 2.01/0.64  fof(f408,plain,(
% 2.01/0.64    ~v4_relat_1(sK5,sK3) | sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5) | ~spl6_45),
% 2.01/0.64    inference(resolution,[],[f381,f84])).
% 2.01/0.64  fof(f84,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f42])).
% 2.01/0.64  fof(f42,plain,(
% 2.01/0.64    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.01/0.64    inference(flattening,[],[f41])).
% 2.01/0.64  fof(f41,plain,(
% 2.01/0.64    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.01/0.64    inference(ennf_transformation,[],[f18])).
% 2.01/0.64  fof(f18,axiom,(
% 2.01/0.64    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 2.01/0.64  fof(f381,plain,(
% 2.01/0.64    v1_partfun1(sK5,sK3) | ~spl6_45),
% 2.01/0.64    inference(avatar_component_clause,[],[f379])).
% 2.01/0.64  fof(f407,plain,(
% 2.01/0.64    spl6_50 | ~spl6_13 | ~spl6_11),
% 2.01/0.64    inference(avatar_split_clause,[],[f398,f153,f163,f405])).
% 2.01/0.64  fof(f398,plain,(
% 2.01/0.64    ( ! [X1] : (~v1_funct_1(sK5) | k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl6_11),
% 2.01/0.64    inference(resolution,[],[f90,f155])).
% 2.01/0.64  fof(f90,plain,(
% 2.01/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f47])).
% 2.01/0.64  fof(f47,plain,(
% 2.01/0.64    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.01/0.64    inference(flattening,[],[f46])).
% 2.01/0.64  fof(f46,plain,(
% 2.01/0.64    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.01/0.64    inference(ennf_transformation,[],[f19])).
% 2.01/0.64  fof(f19,axiom,(
% 2.01/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.01/0.64  fof(f403,plain,(
% 2.01/0.64    spl6_49 | ~spl6_10 | ~spl6_8),
% 2.01/0.64    inference(avatar_split_clause,[],[f397,f138,f148,f401])).
% 2.01/0.64  fof(f397,plain,(
% 2.01/0.64    ( ! [X0] : (~v1_funct_1(sK4) | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl6_8),
% 2.01/0.64    inference(resolution,[],[f90,f140])).
% 2.01/0.64  fof(f396,plain,(
% 2.01/0.64    ~spl6_25 | spl6_48 | ~spl6_31 | ~spl6_44),
% 2.01/0.64    inference(avatar_split_clause,[],[f391,f374,f266,f393,f225])).
% 2.01/0.64  fof(f266,plain,(
% 2.01/0.64    spl6_31 <=> v4_relat_1(sK4,sK2)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 2.01/0.64  fof(f374,plain,(
% 2.01/0.64    spl6_44 <=> v1_partfun1(sK4,sK2)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 2.01/0.64  fof(f391,plain,(
% 2.01/0.64    ~v4_relat_1(sK4,sK2) | sK2 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl6_44),
% 2.01/0.64    inference(resolution,[],[f376,f84])).
% 2.01/0.64  fof(f376,plain,(
% 2.01/0.64    v1_partfun1(sK4,sK2) | ~spl6_44),
% 2.01/0.64    inference(avatar_component_clause,[],[f374])).
% 2.01/0.64  fof(f382,plain,(
% 2.01/0.64    spl6_45 | ~spl6_12 | ~spl6_13 | spl6_2 | ~spl6_11),
% 2.01/0.64    inference(avatar_split_clause,[],[f371,f153,f108,f163,f158,f379])).
% 2.01/0.64  fof(f371,plain,(
% 2.01/0.64    v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3) | ~spl6_11),
% 2.01/0.64    inference(resolution,[],[f75,f155])).
% 2.01/0.64  fof(f75,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f35])).
% 2.01/0.64  fof(f35,plain,(
% 2.01/0.64    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.01/0.64    inference(flattening,[],[f34])).
% 2.01/0.64  fof(f34,plain,(
% 2.01/0.64    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.01/0.64    inference(ennf_transformation,[],[f17])).
% 2.01/0.64  fof(f17,axiom,(
% 2.01/0.64    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 2.01/0.64  fof(f377,plain,(
% 2.01/0.64    spl6_44 | ~spl6_9 | ~spl6_10 | spl6_2 | ~spl6_8),
% 2.01/0.64    inference(avatar_split_clause,[],[f370,f138,f108,f148,f143,f374])).
% 2.01/0.64  fof(f370,plain,(
% 2.01/0.64    v1_xboole_0(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2) | ~spl6_8),
% 2.01/0.64    inference(resolution,[],[f75,f140])).
% 2.01/0.64  fof(f287,plain,(
% 2.01/0.64    spl6_34 | ~spl6_33),
% 2.01/0.64    inference(avatar_split_clause,[],[f282,f277,f284])).
% 2.01/0.64  fof(f282,plain,(
% 2.01/0.64    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl6_33),
% 2.01/0.64    inference(resolution,[],[f279,f94])).
% 2.01/0.64  fof(f94,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.01/0.64    inference(definition_unfolding,[],[f86,f74])).
% 2.01/0.64  fof(f86,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f1])).
% 2.01/0.64  fof(f1,axiom,(
% 2.01/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.01/0.64  fof(f280,plain,(
% 2.01/0.64    spl6_4 | spl6_33 | spl6_7 | ~spl6_5),
% 2.01/0.64    inference(avatar_split_clause,[],[f275,f123,f133,f277,f118])).
% 2.01/0.64  fof(f123,plain,(
% 2.01/0.64    spl6_5 <=> r1_subset_1(sK2,sK3)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.01/0.64  fof(f275,plain,(
% 2.01/0.64    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | ~spl6_5),
% 2.01/0.64    inference(resolution,[],[f82,f125])).
% 2.01/0.64  fof(f125,plain,(
% 2.01/0.64    r1_subset_1(sK2,sK3) | ~spl6_5),
% 2.01/0.64    inference(avatar_component_clause,[],[f123])).
% 2.01/0.64  fof(f82,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f40])).
% 2.01/0.64  fof(f40,plain,(
% 2.01/0.64    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.01/0.64    inference(flattening,[],[f39])).
% 2.01/0.64  fof(f39,plain,(
% 2.01/0.64    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.01/0.64    inference(ennf_transformation,[],[f14])).
% 2.01/0.64  fof(f14,axiom,(
% 2.01/0.64    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 2.01/0.64  fof(f274,plain,(
% 2.01/0.64    spl6_32 | ~spl6_11),
% 2.01/0.64    inference(avatar_split_clause,[],[f263,f153,f271])).
% 2.01/0.64  fof(f263,plain,(
% 2.01/0.64    v4_relat_1(sK5,sK3) | ~spl6_11),
% 2.01/0.64    inference(resolution,[],[f89,f155])).
% 2.01/0.64  fof(f89,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f45])).
% 2.01/0.64  fof(f45,plain,(
% 2.01/0.64    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.64    inference(ennf_transformation,[],[f24])).
% 2.01/0.64  fof(f24,plain,(
% 2.01/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.01/0.64    inference(pure_predicate_removal,[],[f16])).
% 2.01/0.64  fof(f16,axiom,(
% 2.01/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.01/0.64  fof(f269,plain,(
% 2.01/0.64    spl6_31 | ~spl6_8),
% 2.01/0.64    inference(avatar_split_clause,[],[f262,f138,f266])).
% 2.01/0.64  fof(f262,plain,(
% 2.01/0.64    v4_relat_1(sK4,sK2) | ~spl6_8),
% 2.01/0.64    inference(resolution,[],[f89,f140])).
% 2.01/0.64  fof(f261,plain,(
% 2.01/0.64    spl6_30 | ~spl6_17 | ~spl6_18 | ~spl6_27),
% 2.01/0.64    inference(avatar_split_clause,[],[f256,f235,f186,f181,f258])).
% 2.01/0.64  fof(f181,plain,(
% 2.01/0.64    spl6_17 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 2.01/0.64  fof(f235,plain,(
% 2.01/0.64    spl6_27 <=> v1_relat_1(k1_xboole_0)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 2.01/0.64  fof(f256,plain,(
% 2.01/0.64    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | (~spl6_17 | ~spl6_18 | ~spl6_27)),
% 2.01/0.64    inference(forward_demodulation,[],[f255,f183])).
% 2.01/0.64  fof(f183,plain,(
% 2.01/0.64    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl6_17),
% 2.01/0.64    inference(avatar_component_clause,[],[f181])).
% 2.01/0.64  fof(f255,plain,(
% 2.01/0.64    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) | (~spl6_18 | ~spl6_27)),
% 2.01/0.64    inference(forward_demodulation,[],[f253,f188])).
% 2.01/0.64  fof(f253,plain,(
% 2.01/0.64    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) | ~spl6_27),
% 2.01/0.64    inference(resolution,[],[f237,f70])).
% 2.01/0.64  fof(f70,plain,(
% 2.01/0.64    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f30])).
% 2.01/0.64  fof(f30,plain,(
% 2.01/0.64    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.01/0.64    inference(ennf_transformation,[],[f7])).
% 2.01/0.64  fof(f7,axiom,(
% 2.01/0.64    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 2.01/0.64  fof(f237,plain,(
% 2.01/0.64    v1_relat_1(k1_xboole_0) | ~spl6_27),
% 2.01/0.64    inference(avatar_component_clause,[],[f235])).
% 2.01/0.64  fof(f238,plain,(
% 2.01/0.64    spl6_27),
% 2.01/0.64    inference(avatar_split_clause,[],[f223,f235])).
% 2.01/0.64  fof(f223,plain,(
% 2.01/0.64    v1_relat_1(k1_xboole_0)),
% 2.01/0.64    inference(resolution,[],[f88,f66])).
% 2.01/0.64  fof(f66,plain,(
% 2.01/0.64    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.01/0.64    inference(cnf_transformation,[],[f3])).
% 2.01/0.64  fof(f3,axiom,(
% 2.01/0.64    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.01/0.64  fof(f88,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f44])).
% 2.01/0.64  fof(f44,plain,(
% 2.01/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.64    inference(ennf_transformation,[],[f15])).
% 2.01/0.64  fof(f15,axiom,(
% 2.01/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.01/0.64  fof(f233,plain,(
% 2.01/0.64    spl6_26 | ~spl6_11),
% 2.01/0.64    inference(avatar_split_clause,[],[f222,f153,f230])).
% 2.01/0.64  fof(f222,plain,(
% 2.01/0.64    v1_relat_1(sK5) | ~spl6_11),
% 2.01/0.64    inference(resolution,[],[f88,f155])).
% 2.01/0.64  fof(f228,plain,(
% 2.01/0.64    spl6_25 | ~spl6_8),
% 2.01/0.64    inference(avatar_split_clause,[],[f221,f138,f225])).
% 2.01/0.64  fof(f221,plain,(
% 2.01/0.64    v1_relat_1(sK4) | ~spl6_8),
% 2.01/0.64    inference(resolution,[],[f88,f140])).
% 2.01/0.64  fof(f189,plain,(
% 2.01/0.64    spl6_18),
% 2.01/0.64    inference(avatar_split_clause,[],[f64,f186])).
% 2.01/0.64  fof(f64,plain,(
% 2.01/0.64    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.01/0.64    inference(cnf_transformation,[],[f11])).
% 2.01/0.64  fof(f11,axiom,(
% 2.01/0.64    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 2.01/0.64  fof(f184,plain,(
% 2.01/0.64    spl6_17),
% 2.01/0.64    inference(avatar_split_clause,[],[f65,f181])).
% 2.01/0.64  fof(f65,plain,(
% 2.01/0.64    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.01/0.64    inference(cnf_transformation,[],[f11])).
% 2.01/0.64  fof(f179,plain,(
% 2.01/0.64    ~spl6_14 | ~spl6_15 | ~spl6_16),
% 2.01/0.64    inference(avatar_split_clause,[],[f50,f176,f172,f168])).
% 2.01/0.64  fof(f50,plain,(
% 2.01/0.64    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 2.01/0.64    inference(cnf_transformation,[],[f27])).
% 2.01/0.64  fof(f27,plain,(
% 2.01/0.64    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.01/0.64    inference(flattening,[],[f26])).
% 2.01/0.64  fof(f26,plain,(
% 2.01/0.64    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.01/0.64    inference(ennf_transformation,[],[f23])).
% 2.01/0.64  fof(f23,negated_conjecture,(
% 2.01/0.64    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 2.01/0.64    inference(negated_conjecture,[],[f22])).
% 2.01/0.64  fof(f22,conjecture,(
% 2.01/0.64    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 2.01/0.64  fof(f166,plain,(
% 2.01/0.64    spl6_13),
% 2.01/0.64    inference(avatar_split_clause,[],[f51,f163])).
% 2.01/0.64  fof(f51,plain,(
% 2.01/0.64    v1_funct_1(sK5)),
% 2.01/0.64    inference(cnf_transformation,[],[f27])).
% 2.01/0.64  fof(f161,plain,(
% 2.01/0.64    spl6_12),
% 2.01/0.64    inference(avatar_split_clause,[],[f52,f158])).
% 2.01/0.64  fof(f52,plain,(
% 2.01/0.64    v1_funct_2(sK5,sK3,sK1)),
% 2.01/0.64    inference(cnf_transformation,[],[f27])).
% 2.01/0.64  fof(f156,plain,(
% 2.01/0.64    spl6_11),
% 2.01/0.64    inference(avatar_split_clause,[],[f53,f153])).
% 2.01/0.64  fof(f53,plain,(
% 2.01/0.64    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.01/0.64    inference(cnf_transformation,[],[f27])).
% 2.01/0.64  fof(f151,plain,(
% 2.01/0.64    spl6_10),
% 2.01/0.64    inference(avatar_split_clause,[],[f54,f148])).
% 2.01/0.64  fof(f54,plain,(
% 2.01/0.64    v1_funct_1(sK4)),
% 2.01/0.64    inference(cnf_transformation,[],[f27])).
% 2.01/0.64  fof(f146,plain,(
% 2.01/0.64    spl6_9),
% 2.01/0.64    inference(avatar_split_clause,[],[f55,f143])).
% 2.01/0.64  fof(f55,plain,(
% 2.01/0.64    v1_funct_2(sK4,sK2,sK1)),
% 2.01/0.64    inference(cnf_transformation,[],[f27])).
% 2.01/0.64  fof(f141,plain,(
% 2.01/0.64    spl6_8),
% 2.01/0.64    inference(avatar_split_clause,[],[f56,f138])).
% 2.01/0.64  fof(f56,plain,(
% 2.01/0.64    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.01/0.64    inference(cnf_transformation,[],[f27])).
% 2.01/0.64  fof(f136,plain,(
% 2.01/0.64    ~spl6_7),
% 2.01/0.64    inference(avatar_split_clause,[],[f57,f133])).
% 2.01/0.64  fof(f57,plain,(
% 2.01/0.64    ~v1_xboole_0(sK3)),
% 2.01/0.64    inference(cnf_transformation,[],[f27])).
% 2.01/0.64  fof(f131,plain,(
% 2.01/0.64    spl6_6),
% 2.01/0.64    inference(avatar_split_clause,[],[f58,f128])).
% 2.01/0.64  fof(f58,plain,(
% 2.01/0.64    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.01/0.64    inference(cnf_transformation,[],[f27])).
% 2.01/0.64  fof(f126,plain,(
% 2.01/0.64    spl6_5),
% 2.01/0.64    inference(avatar_split_clause,[],[f59,f123])).
% 2.01/0.64  fof(f59,plain,(
% 2.01/0.64    r1_subset_1(sK2,sK3)),
% 2.01/0.64    inference(cnf_transformation,[],[f27])).
% 2.01/0.64  fof(f121,plain,(
% 2.01/0.64    ~spl6_4),
% 2.01/0.64    inference(avatar_split_clause,[],[f60,f118])).
% 2.01/0.64  fof(f60,plain,(
% 2.01/0.64    ~v1_xboole_0(sK2)),
% 2.01/0.64    inference(cnf_transformation,[],[f27])).
% 2.01/0.64  fof(f116,plain,(
% 2.01/0.64    spl6_3),
% 2.01/0.64    inference(avatar_split_clause,[],[f61,f113])).
% 2.01/0.64  fof(f61,plain,(
% 2.01/0.64    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.01/0.64    inference(cnf_transformation,[],[f27])).
% 2.01/0.64  fof(f111,plain,(
% 2.01/0.64    ~spl6_2),
% 2.01/0.64    inference(avatar_split_clause,[],[f62,f108])).
% 2.01/0.64  fof(f62,plain,(
% 2.01/0.64    ~v1_xboole_0(sK1)),
% 2.01/0.64    inference(cnf_transformation,[],[f27])).
% 2.01/0.64  fof(f106,plain,(
% 2.01/0.64    ~spl6_1),
% 2.01/0.64    inference(avatar_split_clause,[],[f63,f103])).
% 2.01/0.64  fof(f63,plain,(
% 2.01/0.64    ~v1_xboole_0(sK0)),
% 2.01/0.64    inference(cnf_transformation,[],[f27])).
% 2.01/0.64  % SZS output end Proof for theBenchmark
% 2.01/0.64  % (28860)------------------------------
% 2.01/0.64  % (28860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.64  % (28860)Termination reason: Refutation
% 2.01/0.64  
% 2.01/0.64  % (28860)Memory used [KB]: 11769
% 2.01/0.64  % (28860)Time elapsed: 0.231 s
% 2.01/0.64  % (28860)------------------------------
% 2.01/0.64  % (28860)------------------------------
% 2.22/0.66  % (28835)Success in time 0.293 s
%------------------------------------------------------------------------------
