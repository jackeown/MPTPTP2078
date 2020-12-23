%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  333 ( 751 expanded)
%              Number of leaves         :   79 ( 371 expanded)
%              Depth                    :   14
%              Number of atoms          : 1577 (3399 expanded)
%              Number of equality atoms :  182 ( 494 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1159,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f153,f158,f163,f176,f186,f215,f220,f239,f244,f250,f256,f266,f273,f329,f334,f340,f346,f352,f356,f369,f373,f377,f381,f393,f413,f425,f442,f450,f454,f466,f476,f484,f539,f545,f567,f583,f597,f604,f619,f640,f670,f680,f703,f766,f797,f821,f828,f843,f1072,f1080,f1158])).

fof(f1158,plain,
    ( ~ spl6_81
    | ~ spl6_6
    | spl6_16
    | ~ spl6_32
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_112 ),
    inference(avatar_split_clause,[],[f1157,f840,f354,f350,f270,f173,f125,f616])).

fof(f616,plain,
    ( spl6_81
  <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).

fof(f125,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f173,plain,
    ( spl6_16
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f270,plain,
    ( spl6_32
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f350,plain,
    ( spl6_37
  <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f354,plain,
    ( spl6_38
  <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f840,plain,
    ( spl6_112
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_112])])).

fof(f1157,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_6
    | spl6_16
    | ~ spl6_32
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_112 ),
    inference(forward_demodulation,[],[f1156,f842])).

fof(f842,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_112 ),
    inference(avatar_component_clause,[],[f840])).

fof(f1156,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_6
    | spl6_16
    | ~ spl6_32
    | ~ spl6_37
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f1155,f351])).

fof(f351,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f350])).

fof(f1155,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl6_6
    | spl6_16
    | ~ spl6_32
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f1154,f272])).

fof(f272,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f270])).

fof(f1154,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl6_6
    | spl6_16
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f1153,f309])).

fof(f309,plain,
    ( ! [X1] : k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))
    | ~ spl6_6 ),
    inference(resolution,[],[f93,f127])).

fof(f127,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f84,f69])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f1153,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_16
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f175,f355])).

fof(f355,plain,
    ( ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f354])).

fof(f175,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f173])).

fof(f1080,plain,
    ( spl6_14
    | spl6_1
    | ~ spl6_102
    | ~ spl6_94
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
    | ~ spl6_32
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_81
    | ~ spl6_106
    | ~ spl6_112 ),
    inference(avatar_split_clause,[],[f1079,f840,f794,f616,f354,f350,f270,f125,f105,f115,f110,f130,f125,f145,f140,f135,f160,f155,f150,f700,f763,f100,f165])).

fof(f165,plain,
    ( spl6_14
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f100,plain,
    ( spl6_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f763,plain,
    ( spl6_102
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).

fof(f700,plain,
    ( spl6_94
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f150,plain,
    ( spl6_11
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f155,plain,
    ( spl6_12
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f160,plain,
    ( spl6_13
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f135,plain,
    ( spl6_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f140,plain,
    ( spl6_9
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f145,plain,
    ( spl6_10
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f130,plain,
    ( spl6_7
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f110,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f115,plain,
    ( spl6_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f105,plain,
    ( spl6_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f794,plain,
    ( spl6_106
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_106])])).

fof(f1079,plain,
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
    | ~ spl6_32
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_81
    | ~ spl6_106
    | ~ spl6_112 ),
    inference(trivial_inequality_removal,[],[f1078])).

fof(f1078,plain,
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
    | ~ spl6_32
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_81
    | ~ spl6_106
    | ~ spl6_112 ),
    inference(forward_demodulation,[],[f1077,f618])).

fof(f618,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_81 ),
    inference(avatar_component_clause,[],[f616])).

fof(f1077,plain,
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
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_106
    | ~ spl6_112 ),
    inference(forward_demodulation,[],[f1076,f842])).

fof(f1076,plain,
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
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_106 ),
    inference(forward_demodulation,[],[f1075,f351])).

fof(f1075,plain,
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
    | ~ spl6_32
    | ~ spl6_38
    | ~ spl6_106 ),
    inference(forward_demodulation,[],[f1074,f272])).

fof(f1074,plain,
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
    | ~ spl6_38
    | ~ spl6_106 ),
    inference(forward_demodulation,[],[f1073,f309])).

fof(f1073,plain,
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
    | ~ spl6_38
    | ~ spl6_106 ),
    inference(forward_demodulation,[],[f1049,f355])).

fof(f1049,plain,
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
    | ~ spl6_106 ),
    inference(resolution,[],[f796,f96])).

fof(f96,plain,(
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
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f26])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f796,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_106 ),
    inference(avatar_component_clause,[],[f794])).

fof(f1072,plain,
    ( spl6_15
    | spl6_1
    | ~ spl6_102
    | ~ spl6_94
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
    | ~ spl6_32
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_81
    | ~ spl6_106
    | ~ spl6_112 ),
    inference(avatar_split_clause,[],[f1071,f840,f794,f616,f354,f350,f270,f125,f105,f115,f110,f130,f125,f145,f140,f135,f160,f155,f150,f700,f763,f100,f169])).

fof(f169,plain,
    ( spl6_15
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f1071,plain,
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
    | ~ spl6_32
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_81
    | ~ spl6_106
    | ~ spl6_112 ),
    inference(trivial_inequality_removal,[],[f1070])).

fof(f1070,plain,
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
    | ~ spl6_32
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_81
    | ~ spl6_106
    | ~ spl6_112 ),
    inference(forward_demodulation,[],[f1069,f618])).

fof(f1069,plain,
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
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_106
    | ~ spl6_112 ),
    inference(forward_demodulation,[],[f1068,f842])).

fof(f1068,plain,
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
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_106 ),
    inference(forward_demodulation,[],[f1067,f351])).

fof(f1067,plain,
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
    | ~ spl6_32
    | ~ spl6_38
    | ~ spl6_106 ),
    inference(forward_demodulation,[],[f1066,f272])).

fof(f1066,plain,
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
    | ~ spl6_38
    | ~ spl6_106 ),
    inference(forward_demodulation,[],[f1065,f309])).

fof(f1065,plain,
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
    | ~ spl6_38
    | ~ spl6_106 ),
    inference(forward_demodulation,[],[f1048,f355])).

fof(f1048,plain,
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
    | ~ spl6_106 ),
    inference(resolution,[],[f796,f97])).

fof(f97,plain,(
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
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f843,plain,
    ( spl6_112
    | ~ spl6_42
    | ~ spl6_110 ),
    inference(avatar_split_clause,[],[f831,f825,f379,f840])).

fof(f379,plain,
    ( spl6_42
  <=> ! [X2] :
        ( ~ r1_xboole_0(X2,sK2)
        | k1_xboole_0 = k7_relat_1(sK4,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f825,plain,
    ( spl6_110
  <=> r1_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).

fof(f831,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_42
    | ~ spl6_110 ),
    inference(resolution,[],[f827,f380])).

fof(f380,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK2)
        | k1_xboole_0 = k7_relat_1(sK4,X2) )
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f379])).

fof(f827,plain,
    ( r1_xboole_0(k1_xboole_0,sK2)
    | ~ spl6_110 ),
    inference(avatar_component_clause,[],[f825])).

fof(f828,plain,
    ( spl6_110
    | ~ spl6_18
    | ~ spl6_25
    | ~ spl6_109 ),
    inference(avatar_split_clause,[],[f823,f818,f225,f183,f825])).

fof(f183,plain,
    ( spl6_18
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f225,plain,
    ( spl6_25
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f818,plain,
    ( spl6_109
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_109])])).

fof(f823,plain,
    ( r1_xboole_0(k1_xboole_0,sK2)
    | ~ spl6_18
    | ~ spl6_25
    | ~ spl6_109 ),
    inference(trivial_inequality_removal,[],[f822])).

fof(f822,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,sK2)
    | ~ spl6_18
    | ~ spl6_25
    | ~ spl6_109 ),
    inference(superposition,[],[f511,f820])).

fof(f820,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,sK2)
    | ~ spl6_109 ),
    inference(avatar_component_clause,[],[f818])).

fof(f511,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k9_relat_1(k1_xboole_0,X3)
        | r1_xboole_0(k1_xboole_0,X3) )
    | ~ spl6_18
    | ~ spl6_25 ),
    inference(forward_demodulation,[],[f508,f185])).

fof(f185,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f183])).

fof(f508,plain,
    ( ! [X3] :
        ( r1_xboole_0(k1_relat_1(k1_xboole_0),X3)
        | k1_xboole_0 != k9_relat_1(k1_xboole_0,X3) )
    | ~ spl6_25 ),
    inference(resolution,[],[f226,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f226,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f225])).

fof(f821,plain,
    ( spl6_109
    | ~ spl6_76
    | ~ spl6_85
    | ~ spl6_90 ),
    inference(avatar_split_clause,[],[f816,f677,f637,f580,f818])).

fof(f580,plain,
    ( spl6_76
  <=> k1_xboole_0 = k7_relat_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f637,plain,
    ( spl6_85
  <=> k9_relat_1(k7_relat_1(sK5,sK2),sK2) = k9_relat_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f677,plain,
    ( spl6_90
  <=> k1_xboole_0 = k9_relat_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f816,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,sK2)
    | ~ spl6_76
    | ~ spl6_85
    | ~ spl6_90 ),
    inference(forward_demodulation,[],[f815,f582])).

fof(f582,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f580])).

fof(f815,plain,
    ( k1_xboole_0 = k9_relat_1(k7_relat_1(sK5,sK2),sK2)
    | ~ spl6_85
    | ~ spl6_90 ),
    inference(forward_demodulation,[],[f639,f679])).

fof(f679,plain,
    ( k1_xboole_0 = k9_relat_1(sK5,sK2)
    | ~ spl6_90 ),
    inference(avatar_component_clause,[],[f677])).

fof(f639,plain,
    ( k9_relat_1(k7_relat_1(sK5,sK2),sK2) = k9_relat_1(sK5,sK2)
    | ~ spl6_85 ),
    inference(avatar_component_clause,[],[f637])).

fof(f797,plain,
    ( spl6_106
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_73 ),
    inference(avatar_split_clause,[],[f792,f565,f135,f140,f145,f794])).

fof(f565,plain,
    ( spl6_73
  <=> ! [X1] :
        ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f792,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_8
    | ~ spl6_73 ),
    inference(resolution,[],[f566,f137])).

fof(f137,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f566,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) )
    | ~ spl6_73 ),
    inference(avatar_component_clause,[],[f565])).

fof(f766,plain,
    ( spl6_102
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f761,f537,f135,f140,f145,f763])).

fof(f537,plain,
    ( spl6_68
  <=> ! [X1] :
        ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f761,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_8
    | ~ spl6_68 ),
    inference(resolution,[],[f538,f137])).

fof(f538,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) )
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f537])).

fof(f703,plain,
    ( spl6_94
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_59 ),
    inference(avatar_split_clause,[],[f698,f474,f135,f140,f145,f700])).

fof(f474,plain,
    ( spl6_59
  <=> ! [X1] :
        ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f698,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_8
    | ~ spl6_59 ),
    inference(resolution,[],[f475,f137])).

fof(f475,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) )
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f474])).

fof(f680,plain,
    ( spl6_90
    | ~ spl6_54
    | ~ spl6_89 ),
    inference(avatar_split_clause,[],[f671,f667,f448,f677])).

fof(f448,plain,
    ( spl6_54
  <=> ! [X1] :
        ( ~ r1_xboole_0(sK3,X1)
        | k1_xboole_0 = k9_relat_1(sK5,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f667,plain,
    ( spl6_89
  <=> r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).

fof(f671,plain,
    ( k1_xboole_0 = k9_relat_1(sK5,sK2)
    | ~ spl6_54
    | ~ spl6_89 ),
    inference(resolution,[],[f669,f449])).

fof(f449,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(sK3,X1)
        | k1_xboole_0 = k9_relat_1(sK5,X1) )
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f448])).

fof(f669,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl6_89 ),
    inference(avatar_component_clause,[],[f667])).

fof(f670,plain,
    ( spl6_89
    | ~ spl6_24
    | ~ spl6_36
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f665,f580,f343,f217,f667])).

fof(f217,plain,
    ( spl6_24
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f343,plain,
    ( spl6_36
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f665,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl6_24
    | ~ spl6_36
    | ~ spl6_76 ),
    inference(trivial_inequality_removal,[],[f660])).

fof(f660,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK3,sK2)
    | ~ spl6_24
    | ~ spl6_36
    | ~ spl6_76 ),
    inference(superposition,[],[f430,f582])).

fof(f430,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k7_relat_1(sK5,X1)
        | r1_xboole_0(sK3,X1) )
    | ~ spl6_24
    | ~ spl6_36 ),
    inference(backward_demodulation,[],[f296,f345])).

fof(f345,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f343])).

fof(f296,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k7_relat_1(sK5,X1)
        | r1_xboole_0(k1_relat_1(sK5),X1) )
    | ~ spl6_24 ),
    inference(resolution,[],[f77,f219])).

fof(f219,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f217])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f640,plain,
    ( spl6_85
    | ~ spl6_24
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f634,f366,f217,f637])).

fof(f366,plain,
    ( spl6_39
  <=> r1_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f634,plain,
    ( k9_relat_1(k7_relat_1(sK5,sK2),sK2) = k9_relat_1(sK5,sK2)
    | ~ spl6_24
    | ~ spl6_39 ),
    inference(resolution,[],[f313,f368])).

fof(f368,plain,
    ( r1_tarski(sK2,sK2)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f366])).

fof(f313,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k9_relat_1(k7_relat_1(sK5,X3),X2) = k9_relat_1(sK5,X2) )
    | ~ spl6_24 ),
    inference(resolution,[],[f67,f219])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f619,plain,
    ( spl6_81
    | ~ spl6_55
    | ~ spl6_79 ),
    inference(avatar_split_clause,[],[f607,f601,f452,f616])).

fof(f452,plain,
    ( spl6_55
  <=> ! [X2] :
        ( ~ r1_xboole_0(X2,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f601,plain,
    ( spl6_79
  <=> r1_xboole_0(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f607,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_55
    | ~ spl6_79 ),
    inference(resolution,[],[f603,f453])).

fof(f453,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X2) )
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f452])).

fof(f603,plain,
    ( r1_xboole_0(k1_xboole_0,sK3)
    | ~ spl6_79 ),
    inference(avatar_component_clause,[],[f601])).

fof(f604,plain,
    ( spl6_79
    | ~ spl6_18
    | ~ spl6_25
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f599,f594,f225,f183,f601])).

fof(f594,plain,
    ( spl6_78
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f599,plain,
    ( r1_xboole_0(k1_xboole_0,sK3)
    | ~ spl6_18
    | ~ spl6_25
    | ~ spl6_78 ),
    inference(trivial_inequality_removal,[],[f598])).

fof(f598,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,sK3)
    | ~ spl6_18
    | ~ spl6_25
    | ~ spl6_78 ),
    inference(superposition,[],[f511,f596])).

fof(f596,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,sK3)
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f594])).

fof(f597,plain,
    ( spl6_78
    | ~ spl6_23
    | ~ spl6_52
    | ~ spl6_57
    | ~ spl6_69 ),
    inference(avatar_split_clause,[],[f592,f542,f463,f439,f212,f594])).

fof(f212,plain,
    ( spl6_23
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f439,plain,
    ( spl6_52
  <=> r1_tarski(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f463,plain,
    ( spl6_57
  <=> k1_xboole_0 = k7_relat_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f542,plain,
    ( spl6_69
  <=> k1_xboole_0 = k9_relat_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f592,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,sK3)
    | ~ spl6_23
    | ~ spl6_52
    | ~ spl6_57
    | ~ spl6_69 ),
    inference(forward_demodulation,[],[f591,f544])).

fof(f544,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,sK3)
    | ~ spl6_69 ),
    inference(avatar_component_clause,[],[f542])).

fof(f591,plain,
    ( k9_relat_1(sK4,sK3) = k9_relat_1(k1_xboole_0,sK3)
    | ~ spl6_23
    | ~ spl6_52
    | ~ spl6_57 ),
    inference(forward_demodulation,[],[f585,f465])).

fof(f465,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f463])).

fof(f585,plain,
    ( k9_relat_1(sK4,sK3) = k9_relat_1(k7_relat_1(sK4,sK3),sK3)
    | ~ spl6_23
    | ~ spl6_52 ),
    inference(resolution,[],[f312,f441])).

fof(f441,plain,
    ( r1_tarski(sK3,sK3)
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f439])).

fof(f312,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k9_relat_1(sK4,X0) = k9_relat_1(k7_relat_1(sK4,X1),X0) )
    | ~ spl6_23 ),
    inference(resolution,[],[f67,f214])).

fof(f214,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f212])).

fof(f583,plain,
    ( spl6_76
    | ~ spl6_31
    | ~ spl6_55 ),
    inference(avatar_split_clause,[],[f578,f452,f263,f580])).

fof(f263,plain,
    ( spl6_31
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f578,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl6_31
    | ~ spl6_55 ),
    inference(resolution,[],[f453,f265])).

fof(f265,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f263])).

fof(f567,plain,
    ( ~ spl6_6
    | ~ spl6_12
    | spl6_7
    | ~ spl6_13
    | spl6_2
    | spl6_73
    | ~ spl6_11
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f559,f423,f150,f565,f105,f160,f130,f155,f125])).

fof(f423,plain,
    ( spl6_50
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f559,plain,
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
    | ~ spl6_50 ),
    inference(resolution,[],[f424,f152])).

fof(f152,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f424,plain,
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
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f423])).

fof(f545,plain,
    ( spl6_69
    | ~ spl6_31
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f540,f375,f263,f542])).

fof(f375,plain,
    ( spl6_41
  <=> ! [X1] :
        ( ~ r1_xboole_0(sK2,X1)
        | k1_xboole_0 = k9_relat_1(sK4,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f540,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,sK3)
    | ~ spl6_31
    | ~ spl6_41 ),
    inference(resolution,[],[f376,f265])).

fof(f376,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(sK2,X1)
        | k1_xboole_0 = k9_relat_1(sK4,X1) )
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f375])).

fof(f539,plain,
    ( ~ spl6_6
    | ~ spl6_12
    | spl6_7
    | ~ spl6_13
    | spl6_2
    | spl6_68
    | ~ spl6_11
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f531,f411,f150,f537,f105,f160,f130,f155,f125])).

fof(f411,plain,
    ( spl6_48
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f531,plain,
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
    | ~ spl6_48 ),
    inference(resolution,[],[f412,f152])).

fof(f412,plain,
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
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f411])).

fof(f484,plain,
    ( spl6_25
    | ~ spl6_23
    | ~ spl6_57 ),
    inference(avatar_split_clause,[],[f482,f463,f212,f225])).

fof(f482,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_23
    | ~ spl6_57 ),
    inference(superposition,[],[f221,f465])).

fof(f221,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK4,X0))
    | ~ spl6_23 ),
    inference(resolution,[],[f214,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f476,plain,
    ( ~ spl6_6
    | ~ spl6_12
    | spl6_7
    | ~ spl6_13
    | spl6_2
    | spl6_59
    | ~ spl6_11
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f468,f391,f150,f474,f105,f160,f130,f155,f125])).

fof(f391,plain,
    ( spl6_44
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f468,plain,
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
    | ~ spl6_44 ),
    inference(resolution,[],[f392,f152])).

fof(f392,plain,
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
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f391])).

fof(f466,plain,
    ( spl6_57
    | ~ spl6_31
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f461,f371,f263,f463])).

fof(f371,plain,
    ( spl6_40
  <=> ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | k1_xboole_0 = k7_relat_1(sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f461,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl6_31
    | ~ spl6_40 ),
    inference(resolution,[],[f372,f265])).

fof(f372,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f371])).

fof(f454,plain,
    ( ~ spl6_24
    | spl6_55
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f435,f343,f452,f217])).

fof(f435,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK3)
        | ~ v1_relat_1(sK5)
        | k1_xboole_0 = k7_relat_1(sK5,X2) )
    | ~ spl6_36 ),
    inference(superposition,[],[f66,f345])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f450,plain,
    ( ~ spl6_24
    | spl6_54
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f434,f343,f448,f217])).

fof(f434,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(sK3,X1)
        | ~ v1_relat_1(sK5)
        | k1_xboole_0 = k9_relat_1(sK5,X1) )
    | ~ spl6_36 ),
    inference(superposition,[],[f74,f345])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f442,plain,
    ( spl6_52
    | ~ spl6_30
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f432,f343,f253,f439])).

fof(f253,plain,
    ( spl6_30
  <=> r1_tarski(k1_relat_1(sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f432,plain,
    ( r1_tarski(sK3,sK3)
    | ~ spl6_30
    | ~ spl6_36 ),
    inference(backward_demodulation,[],[f255,f345])).

fof(f255,plain,
    ( r1_tarski(k1_relat_1(sK5),sK3)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f253])).

fof(f425,plain,
    ( spl6_1
    | spl6_4
    | spl6_50
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f418,f110,f423,f115,f100])).

fof(f418,plain,
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
    inference(resolution,[],[f90,f112])).

fof(f112,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f110])).

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
      | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f413,plain,
    ( spl6_1
    | spl6_4
    | spl6_48
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f406,f110,f411,f115,f100])).

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
        | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f89,f112])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f393,plain,
    ( spl6_1
    | spl6_4
    | spl6_44
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f386,f110,f391,f115,f100])).

fof(f386,plain,
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
    inference(resolution,[],[f88,f112])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f381,plain,
    ( ~ spl6_23
    | spl6_42
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f362,f337,f379,f212])).

fof(f337,plain,
    ( spl6_35
  <=> sK2 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f362,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,sK2)
        | ~ v1_relat_1(sK4)
        | k1_xboole_0 = k7_relat_1(sK4,X2) )
    | ~ spl6_35 ),
    inference(superposition,[],[f66,f339])).

fof(f339,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f337])).

fof(f377,plain,
    ( ~ spl6_23
    | spl6_41
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f361,f337,f375,f212])).

fof(f361,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(sK2,X1)
        | ~ v1_relat_1(sK4)
        | k1_xboole_0 = k9_relat_1(sK4,X1) )
    | ~ spl6_35 ),
    inference(superposition,[],[f74,f339])).

fof(f373,plain,
    ( ~ spl6_23
    | spl6_40
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f360,f337,f371,f212])).

fof(f360,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | ~ v1_relat_1(sK4)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl6_35 ),
    inference(superposition,[],[f76,f339])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f369,plain,
    ( spl6_39
    | ~ spl6_29
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f359,f337,f247,f366])).

fof(f247,plain,
    ( spl6_29
  <=> r1_tarski(k1_relat_1(sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f359,plain,
    ( r1_tarski(sK2,sK2)
    | ~ spl6_29
    | ~ spl6_35 ),
    inference(backward_demodulation,[],[f249,f339])).

fof(f249,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f247])).

fof(f356,plain,
    ( spl6_38
    | ~ spl6_13
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f348,f150,f160,f354])).

fof(f348,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK5)
        | k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) )
    | ~ spl6_11 ),
    inference(resolution,[],[f87,f152])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f352,plain,
    ( spl6_37
    | ~ spl6_10
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f347,f135,f145,f350])).

fof(f347,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) )
    | ~ spl6_8 ),
    inference(resolution,[],[f87,f137])).

fof(f346,plain,
    ( ~ spl6_24
    | spl6_36
    | ~ spl6_28
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f341,f331,f241,f343,f217])).

% (4115)Refutation not found, incomplete strategy% (4115)------------------------------
% (4115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f241,plain,
    ( spl6_28
  <=> v4_relat_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f331,plain,
    ( spl6_34
  <=> v1_partfun1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f341,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl6_34 ),
    inference(resolution,[],[f333,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f333,plain,
    ( v1_partfun1(sK5,sK3)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f331])).

fof(f340,plain,
    ( ~ spl6_23
    | spl6_35
    | ~ spl6_27
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f335,f326,f236,f337,f212])).

fof(f236,plain,
    ( spl6_27
  <=> v4_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f326,plain,
    ( spl6_33
  <=> v1_partfun1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f335,plain,
    ( ~ v4_relat_1(sK4,sK2)
    | sK2 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl6_33 ),
    inference(resolution,[],[f328,f81])).

fof(f328,plain,
    ( v1_partfun1(sK4,sK2)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f326])).

fof(f334,plain,
    ( spl6_34
    | ~ spl6_12
    | ~ spl6_13
    | spl6_2
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f324,f150,f105,f160,f155,f331])).

fof(f324,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f70,f152])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f329,plain,
    ( spl6_33
    | ~ spl6_9
    | ~ spl6_10
    | spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f323,f135,f105,f145,f140,f326])).

fof(f323,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f70,f137])).

fof(f273,plain,
    ( spl6_32
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f268,f263,f270])).

fof(f268,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl6_31 ),
    inference(resolution,[],[f265,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f83,f69])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f266,plain,
    ( spl6_4
    | spl6_31
    | spl6_7
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f261,f120,f130,f263,f115])).

fof(f120,plain,
    ( spl6_5
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f261,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f79,f122])).

fof(f122,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f256,plain,
    ( ~ spl6_24
    | spl6_30
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f251,f241,f253,f217])).

fof(f251,plain,
    ( r1_tarski(k1_relat_1(sK5),sK3)
    | ~ v1_relat_1(sK5)
    | ~ spl6_28 ),
    inference(resolution,[],[f243,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f243,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f241])).

fof(f250,plain,
    ( ~ spl6_23
    | spl6_29
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f245,f236,f247,f212])).

fof(f245,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4)
    | ~ spl6_27 ),
    inference(resolution,[],[f238,f73])).

fof(f238,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f236])).

fof(f244,plain,
    ( spl6_28
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f234,f150,f241])).

fof(f234,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f86,f152])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f239,plain,
    ( spl6_27
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f233,f135,f236])).

fof(f233,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f86,f137])).

fof(f220,plain,
    ( spl6_24
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f210,f150,f217])).

fof(f210,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_11 ),
    inference(resolution,[],[f85,f152])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f215,plain,
    ( spl6_23
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f209,f135,f212])).

fof(f209,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_8 ),
    inference(resolution,[],[f85,f137])).

fof(f186,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f61,f183])).

fof(f61,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f176,plain,
    ( ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f47,f173,f169,f165])).

fof(f47,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f24])).

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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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

fof(f163,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f48,f160])).

fof(f48,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f158,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f49,f155])).

fof(f49,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f153,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f50,f150])).

fof(f50,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f148,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f51,f145])).

fof(f51,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f143,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f52,f140])).

fof(f52,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f138,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f53,f135])).

fof(f53,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f133,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f54,f130])).

fof(f54,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f128,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f55,f125])).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f123,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f56,f120])).

fof(f56,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f118,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f57,f115])).

fof(f57,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f113,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f58,f110])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f108,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f59,f105])).

fof(f59,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f103,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f60,f100])).

fof(f60,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (4117)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.48  % (4101)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.49  % (4103)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.49  % (4109)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.49  % (4095)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (4100)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (4104)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (4105)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (4108)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (4102)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (4093)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (4122)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (4096)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (4119)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.51  % (4106)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (4097)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (4107)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (4116)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (4098)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (4094)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (4113)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (4121)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (4099)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (4120)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (4112)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (4114)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (4110)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (4111)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (4115)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (4118)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (4110)Refutation not found, incomplete strategy% (4110)------------------------------
% 0.20/0.53  % (4110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4110)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4110)Memory used [KB]: 10746
% 0.20/0.53  % (4110)Time elapsed: 0.137 s
% 0.20/0.53  % (4110)------------------------------
% 0.20/0.53  % (4110)------------------------------
% 0.20/0.54  % (4109)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f1159,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f153,f158,f163,f176,f186,f215,f220,f239,f244,f250,f256,f266,f273,f329,f334,f340,f346,f352,f356,f369,f373,f377,f381,f393,f413,f425,f442,f450,f454,f466,f476,f484,f539,f545,f567,f583,f597,f604,f619,f640,f670,f680,f703,f766,f797,f821,f828,f843,f1072,f1080,f1158])).
% 0.20/0.54  fof(f1158,plain,(
% 0.20/0.54    ~spl6_81 | ~spl6_6 | spl6_16 | ~spl6_32 | ~spl6_37 | ~spl6_38 | ~spl6_112),
% 0.20/0.54    inference(avatar_split_clause,[],[f1157,f840,f354,f350,f270,f173,f125,f616])).
% 0.20/0.54  fof(f616,plain,(
% 0.20/0.54    spl6_81 <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).
% 0.20/0.54  fof(f125,plain,(
% 0.20/0.54    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.54  fof(f173,plain,(
% 0.20/0.54    spl6_16 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.54  fof(f270,plain,(
% 0.20/0.54    spl6_32 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.20/0.54  fof(f350,plain,(
% 0.20/0.54    spl6_37 <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.20/0.54  fof(f354,plain,(
% 0.20/0.54    spl6_38 <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.20/0.54  fof(f840,plain,(
% 0.20/0.54    spl6_112 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_112])])).
% 0.20/0.54  fof(f1157,plain,(
% 0.20/0.54    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | (~spl6_6 | spl6_16 | ~spl6_32 | ~spl6_37 | ~spl6_38 | ~spl6_112)),
% 0.20/0.54    inference(forward_demodulation,[],[f1156,f842])).
% 0.20/0.54  fof(f842,plain,(
% 0.20/0.54    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl6_112),
% 0.20/0.54    inference(avatar_component_clause,[],[f840])).
% 0.20/0.54  fof(f1156,plain,(
% 0.20/0.54    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | (~spl6_6 | spl6_16 | ~spl6_32 | ~spl6_37 | ~spl6_38)),
% 0.20/0.54    inference(forward_demodulation,[],[f1155,f351])).
% 0.20/0.54  fof(f351,plain,(
% 0.20/0.54    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl6_37),
% 0.20/0.54    inference(avatar_component_clause,[],[f350])).
% 0.20/0.54  fof(f1155,plain,(
% 0.20/0.54    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (~spl6_6 | spl6_16 | ~spl6_32 | ~spl6_38)),
% 0.20/0.54    inference(forward_demodulation,[],[f1154,f272])).
% 0.20/0.54  fof(f272,plain,(
% 0.20/0.54    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl6_32),
% 0.20/0.54    inference(avatar_component_clause,[],[f270])).
% 0.20/0.54  fof(f1154,plain,(
% 0.20/0.54    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | (~spl6_6 | spl6_16 | ~spl6_38)),
% 0.20/0.54    inference(forward_demodulation,[],[f1153,f309])).
% 0.20/0.54  fof(f309,plain,(
% 0.20/0.54    ( ! [X1] : (k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))) ) | ~spl6_6),
% 0.20/0.54    inference(resolution,[],[f93,f127])).
% 0.20/0.54  fof(f127,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl6_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f125])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f84,f69])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.54  fof(f1153,plain,(
% 0.20/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (spl6_16 | ~spl6_38)),
% 0.20/0.54    inference(forward_demodulation,[],[f175,f355])).
% 0.20/0.54  fof(f355,plain,(
% 0.20/0.54    ( ! [X1] : (k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl6_38),
% 0.20/0.54    inference(avatar_component_clause,[],[f354])).
% 0.20/0.54  fof(f175,plain,(
% 0.20/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_16),
% 0.20/0.54    inference(avatar_component_clause,[],[f173])).
% 0.20/0.54  fof(f1080,plain,(
% 0.20/0.54    spl6_14 | spl6_1 | ~spl6_102 | ~spl6_94 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_6 | spl6_7 | ~spl6_3 | spl6_4 | spl6_2 | ~spl6_6 | ~spl6_32 | ~spl6_37 | ~spl6_38 | ~spl6_81 | ~spl6_106 | ~spl6_112),
% 0.20/0.54    inference(avatar_split_clause,[],[f1079,f840,f794,f616,f354,f350,f270,f125,f105,f115,f110,f130,f125,f145,f140,f135,f160,f155,f150,f700,f763,f100,f165])).
% 0.20/0.54  fof(f165,plain,(
% 0.20/0.54    spl6_14 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    spl6_1 <=> v1_xboole_0(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.54  fof(f763,plain,(
% 0.20/0.54    spl6_102 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).
% 0.20/0.54  fof(f700,plain,(
% 0.20/0.54    spl6_94 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).
% 0.20/0.54  fof(f150,plain,(
% 0.20/0.54    spl6_11 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.54  fof(f155,plain,(
% 0.20/0.54    spl6_12 <=> v1_funct_2(sK5,sK3,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.54  fof(f160,plain,(
% 0.20/0.54    spl6_13 <=> v1_funct_1(sK5)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.54  fof(f135,plain,(
% 0.20/0.54    spl6_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.54  fof(f140,plain,(
% 0.20/0.54    spl6_9 <=> v1_funct_2(sK4,sK2,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.54  fof(f145,plain,(
% 0.20/0.54    spl6_10 <=> v1_funct_1(sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.54  fof(f130,plain,(
% 0.20/0.54    spl6_7 <=> v1_xboole_0(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.54  fof(f110,plain,(
% 0.20/0.54    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    spl6_4 <=> v1_xboole_0(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.54  fof(f105,plain,(
% 0.20/0.54    spl6_2 <=> v1_xboole_0(sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.54  fof(f794,plain,(
% 0.20/0.54    spl6_106 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_106])])).
% 0.20/0.54  fof(f1079,plain,(
% 0.20/0.54    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_32 | ~spl6_37 | ~spl6_38 | ~spl6_81 | ~spl6_106 | ~spl6_112)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f1078])).
% 0.20/0.54  fof(f1078,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_32 | ~spl6_37 | ~spl6_38 | ~spl6_81 | ~spl6_106 | ~spl6_112)),
% 0.20/0.54    inference(forward_demodulation,[],[f1077,f618])).
% 0.20/0.54  fof(f618,plain,(
% 0.20/0.54    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | ~spl6_81),
% 0.20/0.54    inference(avatar_component_clause,[],[f616])).
% 0.20/0.54  fof(f1077,plain,(
% 0.20/0.54    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_32 | ~spl6_37 | ~spl6_38 | ~spl6_106 | ~spl6_112)),
% 0.20/0.54    inference(forward_demodulation,[],[f1076,f842])).
% 0.20/0.54  fof(f1076,plain,(
% 0.20/0.54    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_32 | ~spl6_37 | ~spl6_38 | ~spl6_106)),
% 0.20/0.54    inference(forward_demodulation,[],[f1075,f351])).
% 0.20/0.54  fof(f1075,plain,(
% 0.20/0.54    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_32 | ~spl6_38 | ~spl6_106)),
% 0.20/0.54    inference(forward_demodulation,[],[f1074,f272])).
% 0.20/0.54  fof(f1074,plain,(
% 0.20/0.54    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_38 | ~spl6_106)),
% 0.20/0.54    inference(forward_demodulation,[],[f1073,f309])).
% 0.20/0.54  fof(f1073,plain,(
% 0.20/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_38 | ~spl6_106)),
% 0.20/0.54    inference(forward_demodulation,[],[f1049,f355])).
% 0.20/0.54  fof(f1049,plain,(
% 0.20/0.54    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~spl6_106),
% 0.20/0.54    inference(resolution,[],[f796,f96])).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 0.20/0.54    inference(equality_resolution,[],[f64])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,axiom,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).
% 0.20/0.54  fof(f796,plain,(
% 0.20/0.54    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl6_106),
% 0.20/0.54    inference(avatar_component_clause,[],[f794])).
% 0.20/0.54  fof(f1072,plain,(
% 0.20/0.54    spl6_15 | spl6_1 | ~spl6_102 | ~spl6_94 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_6 | spl6_7 | ~spl6_3 | spl6_4 | spl6_2 | ~spl6_6 | ~spl6_32 | ~spl6_37 | ~spl6_38 | ~spl6_81 | ~spl6_106 | ~spl6_112),
% 0.20/0.54    inference(avatar_split_clause,[],[f1071,f840,f794,f616,f354,f350,f270,f125,f105,f115,f110,f130,f125,f145,f140,f135,f160,f155,f150,f700,f763,f100,f169])).
% 0.20/0.54  fof(f169,plain,(
% 0.20/0.54    spl6_15 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.54  fof(f1071,plain,(
% 0.20/0.54    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_32 | ~spl6_37 | ~spl6_38 | ~spl6_81 | ~spl6_106 | ~spl6_112)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f1070])).
% 0.20/0.54  fof(f1070,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_32 | ~spl6_37 | ~spl6_38 | ~spl6_81 | ~spl6_106 | ~spl6_112)),
% 0.20/0.54    inference(forward_demodulation,[],[f1069,f618])).
% 0.20/0.54  fof(f1069,plain,(
% 0.20/0.54    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_32 | ~spl6_37 | ~spl6_38 | ~spl6_106 | ~spl6_112)),
% 0.20/0.54    inference(forward_demodulation,[],[f1068,f842])).
% 0.20/0.54  fof(f1068,plain,(
% 0.20/0.54    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_32 | ~spl6_37 | ~spl6_38 | ~spl6_106)),
% 0.20/0.54    inference(forward_demodulation,[],[f1067,f351])).
% 0.20/0.54  fof(f1067,plain,(
% 0.20/0.54    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_32 | ~spl6_38 | ~spl6_106)),
% 0.20/0.54    inference(forward_demodulation,[],[f1066,f272])).
% 0.20/0.54  fof(f1066,plain,(
% 0.20/0.54    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_38 | ~spl6_106)),
% 0.20/0.54    inference(forward_demodulation,[],[f1065,f309])).
% 0.20/0.54  fof(f1065,plain,(
% 0.20/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_38 | ~spl6_106)),
% 0.20/0.54    inference(forward_demodulation,[],[f1048,f355])).
% 0.20/0.54  fof(f1048,plain,(
% 0.20/0.54    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~spl6_106),
% 0.20/0.54    inference(resolution,[],[f796,f97])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 0.20/0.54    inference(equality_resolution,[],[f63])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  fof(f843,plain,(
% 0.20/0.54    spl6_112 | ~spl6_42 | ~spl6_110),
% 0.20/0.54    inference(avatar_split_clause,[],[f831,f825,f379,f840])).
% 0.20/0.54  fof(f379,plain,(
% 0.20/0.54    spl6_42 <=> ! [X2] : (~r1_xboole_0(X2,sK2) | k1_xboole_0 = k7_relat_1(sK4,X2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.20/0.54  fof(f825,plain,(
% 0.20/0.54    spl6_110 <=> r1_xboole_0(k1_xboole_0,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).
% 0.20/0.54  fof(f831,plain,(
% 0.20/0.54    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | (~spl6_42 | ~spl6_110)),
% 0.20/0.54    inference(resolution,[],[f827,f380])).
% 0.20/0.54  fof(f380,plain,(
% 0.20/0.54    ( ! [X2] : (~r1_xboole_0(X2,sK2) | k1_xboole_0 = k7_relat_1(sK4,X2)) ) | ~spl6_42),
% 0.20/0.54    inference(avatar_component_clause,[],[f379])).
% 0.20/0.54  fof(f827,plain,(
% 0.20/0.54    r1_xboole_0(k1_xboole_0,sK2) | ~spl6_110),
% 0.20/0.54    inference(avatar_component_clause,[],[f825])).
% 0.20/0.54  fof(f828,plain,(
% 0.20/0.54    spl6_110 | ~spl6_18 | ~spl6_25 | ~spl6_109),
% 0.20/0.54    inference(avatar_split_clause,[],[f823,f818,f225,f183,f825])).
% 0.20/0.54  fof(f183,plain,(
% 0.20/0.54    spl6_18 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.54  fof(f225,plain,(
% 0.20/0.54    spl6_25 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.20/0.54  fof(f818,plain,(
% 0.20/0.54    spl6_109 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_109])])).
% 0.20/0.54  fof(f823,plain,(
% 0.20/0.54    r1_xboole_0(k1_xboole_0,sK2) | (~spl6_18 | ~spl6_25 | ~spl6_109)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f822])).
% 0.20/0.54  fof(f822,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,sK2) | (~spl6_18 | ~spl6_25 | ~spl6_109)),
% 0.20/0.54    inference(superposition,[],[f511,f820])).
% 0.20/0.54  fof(f820,plain,(
% 0.20/0.54    k1_xboole_0 = k9_relat_1(k1_xboole_0,sK2) | ~spl6_109),
% 0.20/0.54    inference(avatar_component_clause,[],[f818])).
% 0.20/0.54  fof(f511,plain,(
% 0.20/0.54    ( ! [X3] : (k1_xboole_0 != k9_relat_1(k1_xboole_0,X3) | r1_xboole_0(k1_xboole_0,X3)) ) | (~spl6_18 | ~spl6_25)),
% 0.20/0.54    inference(forward_demodulation,[],[f508,f185])).
% 0.20/0.54  fof(f185,plain,(
% 0.20/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_18),
% 0.20/0.54    inference(avatar_component_clause,[],[f183])).
% 0.20/0.54  fof(f508,plain,(
% 0.20/0.54    ( ! [X3] : (r1_xboole_0(k1_relat_1(k1_xboole_0),X3) | k1_xboole_0 != k9_relat_1(k1_xboole_0,X3)) ) | ~spl6_25),
% 0.20/0.54    inference(resolution,[],[f226,f75])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.20/0.54  fof(f226,plain,(
% 0.20/0.54    v1_relat_1(k1_xboole_0) | ~spl6_25),
% 0.20/0.54    inference(avatar_component_clause,[],[f225])).
% 0.20/0.54  fof(f821,plain,(
% 0.20/0.54    spl6_109 | ~spl6_76 | ~spl6_85 | ~spl6_90),
% 0.20/0.54    inference(avatar_split_clause,[],[f816,f677,f637,f580,f818])).
% 0.20/0.54  fof(f580,plain,(
% 0.20/0.54    spl6_76 <=> k1_xboole_0 = k7_relat_1(sK5,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).
% 0.20/0.54  fof(f637,plain,(
% 0.20/0.54    spl6_85 <=> k9_relat_1(k7_relat_1(sK5,sK2),sK2) = k9_relat_1(sK5,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).
% 0.20/0.54  fof(f677,plain,(
% 0.20/0.54    spl6_90 <=> k1_xboole_0 = k9_relat_1(sK5,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).
% 0.20/0.54  fof(f816,plain,(
% 0.20/0.54    k1_xboole_0 = k9_relat_1(k1_xboole_0,sK2) | (~spl6_76 | ~spl6_85 | ~spl6_90)),
% 0.20/0.54    inference(forward_demodulation,[],[f815,f582])).
% 0.20/0.54  fof(f582,plain,(
% 0.20/0.54    k1_xboole_0 = k7_relat_1(sK5,sK2) | ~spl6_76),
% 0.20/0.54    inference(avatar_component_clause,[],[f580])).
% 0.20/0.54  fof(f815,plain,(
% 0.20/0.54    k1_xboole_0 = k9_relat_1(k7_relat_1(sK5,sK2),sK2) | (~spl6_85 | ~spl6_90)),
% 0.20/0.54    inference(forward_demodulation,[],[f639,f679])).
% 0.20/0.54  fof(f679,plain,(
% 0.20/0.54    k1_xboole_0 = k9_relat_1(sK5,sK2) | ~spl6_90),
% 0.20/0.54    inference(avatar_component_clause,[],[f677])).
% 0.20/0.54  fof(f639,plain,(
% 0.20/0.54    k9_relat_1(k7_relat_1(sK5,sK2),sK2) = k9_relat_1(sK5,sK2) | ~spl6_85),
% 0.20/0.54    inference(avatar_component_clause,[],[f637])).
% 0.20/0.54  fof(f797,plain,(
% 0.20/0.54    spl6_106 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_73),
% 0.20/0.54    inference(avatar_split_clause,[],[f792,f565,f135,f140,f145,f794])).
% 0.20/0.54  fof(f565,plain,(
% 0.20/0.54    spl6_73 <=> ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).
% 0.20/0.54  fof(f792,plain,(
% 0.20/0.54    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_8 | ~spl6_73)),
% 0.20/0.54    inference(resolution,[],[f566,f137])).
% 0.20/0.54  fof(f137,plain,(
% 0.20/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl6_8),
% 0.20/0.54    inference(avatar_component_clause,[],[f135])).
% 0.20/0.54  fof(f566,plain,(
% 0.20/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))) ) | ~spl6_73),
% 0.20/0.54    inference(avatar_component_clause,[],[f565])).
% 0.20/0.54  fof(f766,plain,(
% 0.20/0.54    spl6_102 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_68),
% 0.20/0.54    inference(avatar_split_clause,[],[f761,f537,f135,f140,f145,f763])).
% 0.20/0.54  fof(f537,plain,(
% 0.20/0.54    spl6_68 <=> ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 0.20/0.54  fof(f761,plain,(
% 0.20/0.54    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_8 | ~spl6_68)),
% 0.20/0.54    inference(resolution,[],[f538,f137])).
% 0.20/0.54  fof(f538,plain,(
% 0.20/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)) ) | ~spl6_68),
% 0.20/0.54    inference(avatar_component_clause,[],[f537])).
% 0.20/0.54  fof(f703,plain,(
% 0.20/0.54    spl6_94 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_59),
% 0.20/0.54    inference(avatar_split_clause,[],[f698,f474,f135,f140,f145,f700])).
% 0.20/0.54  fof(f474,plain,(
% 0.20/0.54    spl6_59 <=> ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 0.20/0.54  fof(f698,plain,(
% 0.20/0.54    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_8 | ~spl6_59)),
% 0.20/0.54    inference(resolution,[],[f475,f137])).
% 0.20/0.54  fof(f475,plain,(
% 0.20/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))) ) | ~spl6_59),
% 0.20/0.54    inference(avatar_component_clause,[],[f474])).
% 0.20/0.54  fof(f680,plain,(
% 0.20/0.54    spl6_90 | ~spl6_54 | ~spl6_89),
% 0.20/0.54    inference(avatar_split_clause,[],[f671,f667,f448,f677])).
% 0.20/0.54  fof(f448,plain,(
% 0.20/0.54    spl6_54 <=> ! [X1] : (~r1_xboole_0(sK3,X1) | k1_xboole_0 = k9_relat_1(sK5,X1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 0.20/0.54  fof(f667,plain,(
% 0.20/0.54    spl6_89 <=> r1_xboole_0(sK3,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).
% 0.20/0.54  fof(f671,plain,(
% 0.20/0.54    k1_xboole_0 = k9_relat_1(sK5,sK2) | (~spl6_54 | ~spl6_89)),
% 0.20/0.54    inference(resolution,[],[f669,f449])).
% 0.20/0.54  fof(f449,plain,(
% 0.20/0.54    ( ! [X1] : (~r1_xboole_0(sK3,X1) | k1_xboole_0 = k9_relat_1(sK5,X1)) ) | ~spl6_54),
% 0.20/0.54    inference(avatar_component_clause,[],[f448])).
% 0.20/0.54  fof(f669,plain,(
% 0.20/0.54    r1_xboole_0(sK3,sK2) | ~spl6_89),
% 0.20/0.54    inference(avatar_component_clause,[],[f667])).
% 0.20/0.54  fof(f670,plain,(
% 0.20/0.54    spl6_89 | ~spl6_24 | ~spl6_36 | ~spl6_76),
% 0.20/0.54    inference(avatar_split_clause,[],[f665,f580,f343,f217,f667])).
% 0.20/0.54  fof(f217,plain,(
% 0.20/0.54    spl6_24 <=> v1_relat_1(sK5)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.20/0.54  fof(f343,plain,(
% 0.20/0.54    spl6_36 <=> sK3 = k1_relat_1(sK5)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.20/0.54  fof(f665,plain,(
% 0.20/0.54    r1_xboole_0(sK3,sK2) | (~spl6_24 | ~spl6_36 | ~spl6_76)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f660])).
% 0.20/0.54  fof(f660,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK3,sK2) | (~spl6_24 | ~spl6_36 | ~spl6_76)),
% 0.20/0.54    inference(superposition,[],[f430,f582])).
% 0.20/0.54  fof(f430,plain,(
% 0.20/0.54    ( ! [X1] : (k1_xboole_0 != k7_relat_1(sK5,X1) | r1_xboole_0(sK3,X1)) ) | (~spl6_24 | ~spl6_36)),
% 0.20/0.54    inference(backward_demodulation,[],[f296,f345])).
% 0.20/0.54  fof(f345,plain,(
% 0.20/0.54    sK3 = k1_relat_1(sK5) | ~spl6_36),
% 0.20/0.54    inference(avatar_component_clause,[],[f343])).
% 0.20/0.54  fof(f296,plain,(
% 0.20/0.54    ( ! [X1] : (k1_xboole_0 != k7_relat_1(sK5,X1) | r1_xboole_0(k1_relat_1(sK5),X1)) ) | ~spl6_24),
% 0.20/0.54    inference(resolution,[],[f77,f219])).
% 0.20/0.54  fof(f219,plain,(
% 0.20/0.54    v1_relat_1(sK5) | ~spl6_24),
% 0.20/0.54    inference(avatar_component_clause,[],[f217])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.20/0.54  fof(f640,plain,(
% 0.20/0.54    spl6_85 | ~spl6_24 | ~spl6_39),
% 0.20/0.54    inference(avatar_split_clause,[],[f634,f366,f217,f637])).
% 0.20/0.54  fof(f366,plain,(
% 0.20/0.54    spl6_39 <=> r1_tarski(sK2,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.20/0.54  fof(f634,plain,(
% 0.20/0.54    k9_relat_1(k7_relat_1(sK5,sK2),sK2) = k9_relat_1(sK5,sK2) | (~spl6_24 | ~spl6_39)),
% 0.20/0.54    inference(resolution,[],[f313,f368])).
% 0.20/0.54  fof(f368,plain,(
% 0.20/0.54    r1_tarski(sK2,sK2) | ~spl6_39),
% 0.20/0.54    inference(avatar_component_clause,[],[f366])).
% 0.20/0.54  fof(f313,plain,(
% 0.20/0.54    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k9_relat_1(k7_relat_1(sK5,X3),X2) = k9_relat_1(sK5,X2)) ) | ~spl6_24),
% 0.20/0.54    inference(resolution,[],[f67,f219])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 0.20/0.54  fof(f619,plain,(
% 0.20/0.54    spl6_81 | ~spl6_55 | ~spl6_79),
% 0.20/0.54    inference(avatar_split_clause,[],[f607,f601,f452,f616])).
% 0.20/0.54  fof(f452,plain,(
% 0.20/0.54    spl6_55 <=> ! [X2] : (~r1_xboole_0(X2,sK3) | k1_xboole_0 = k7_relat_1(sK5,X2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 0.20/0.54  fof(f601,plain,(
% 0.20/0.54    spl6_79 <=> r1_xboole_0(k1_xboole_0,sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).
% 0.20/0.54  fof(f607,plain,(
% 0.20/0.54    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | (~spl6_55 | ~spl6_79)),
% 0.20/0.54    inference(resolution,[],[f603,f453])).
% 0.20/0.54  fof(f453,plain,(
% 0.20/0.54    ( ! [X2] : (~r1_xboole_0(X2,sK3) | k1_xboole_0 = k7_relat_1(sK5,X2)) ) | ~spl6_55),
% 0.20/0.54    inference(avatar_component_clause,[],[f452])).
% 0.20/0.54  fof(f603,plain,(
% 0.20/0.54    r1_xboole_0(k1_xboole_0,sK3) | ~spl6_79),
% 0.20/0.54    inference(avatar_component_clause,[],[f601])).
% 0.20/0.54  fof(f604,plain,(
% 0.20/0.54    spl6_79 | ~spl6_18 | ~spl6_25 | ~spl6_78),
% 0.20/0.54    inference(avatar_split_clause,[],[f599,f594,f225,f183,f601])).
% 0.20/0.54  fof(f594,plain,(
% 0.20/0.54    spl6_78 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 0.20/0.54  fof(f599,plain,(
% 0.20/0.54    r1_xboole_0(k1_xboole_0,sK3) | (~spl6_18 | ~spl6_25 | ~spl6_78)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f598])).
% 0.20/0.54  fof(f598,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,sK3) | (~spl6_18 | ~spl6_25 | ~spl6_78)),
% 0.20/0.54    inference(superposition,[],[f511,f596])).
% 0.20/0.54  fof(f596,plain,(
% 0.20/0.54    k1_xboole_0 = k9_relat_1(k1_xboole_0,sK3) | ~spl6_78),
% 0.20/0.54    inference(avatar_component_clause,[],[f594])).
% 0.20/0.54  fof(f597,plain,(
% 0.20/0.54    spl6_78 | ~spl6_23 | ~spl6_52 | ~spl6_57 | ~spl6_69),
% 0.20/0.54    inference(avatar_split_clause,[],[f592,f542,f463,f439,f212,f594])).
% 0.20/0.54  fof(f212,plain,(
% 0.20/0.54    spl6_23 <=> v1_relat_1(sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.20/0.54  fof(f439,plain,(
% 0.20/0.54    spl6_52 <=> r1_tarski(sK3,sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 0.20/0.54  fof(f463,plain,(
% 0.20/0.54    spl6_57 <=> k1_xboole_0 = k7_relat_1(sK4,sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 0.20/0.54  fof(f542,plain,(
% 0.20/0.54    spl6_69 <=> k1_xboole_0 = k9_relat_1(sK4,sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).
% 0.20/0.54  fof(f592,plain,(
% 0.20/0.54    k1_xboole_0 = k9_relat_1(k1_xboole_0,sK3) | (~spl6_23 | ~spl6_52 | ~spl6_57 | ~spl6_69)),
% 0.20/0.54    inference(forward_demodulation,[],[f591,f544])).
% 0.20/0.54  fof(f544,plain,(
% 0.20/0.54    k1_xboole_0 = k9_relat_1(sK4,sK3) | ~spl6_69),
% 0.20/0.54    inference(avatar_component_clause,[],[f542])).
% 0.20/0.54  fof(f591,plain,(
% 0.20/0.54    k9_relat_1(sK4,sK3) = k9_relat_1(k1_xboole_0,sK3) | (~spl6_23 | ~spl6_52 | ~spl6_57)),
% 0.20/0.54    inference(forward_demodulation,[],[f585,f465])).
% 0.20/0.54  fof(f465,plain,(
% 0.20/0.54    k1_xboole_0 = k7_relat_1(sK4,sK3) | ~spl6_57),
% 0.20/0.54    inference(avatar_component_clause,[],[f463])).
% 0.20/0.54  fof(f585,plain,(
% 0.20/0.54    k9_relat_1(sK4,sK3) = k9_relat_1(k7_relat_1(sK4,sK3),sK3) | (~spl6_23 | ~spl6_52)),
% 0.20/0.54    inference(resolution,[],[f312,f441])).
% 0.20/0.54  fof(f441,plain,(
% 0.20/0.54    r1_tarski(sK3,sK3) | ~spl6_52),
% 0.20/0.54    inference(avatar_component_clause,[],[f439])).
% 0.20/0.54  fof(f312,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k9_relat_1(sK4,X0) = k9_relat_1(k7_relat_1(sK4,X1),X0)) ) | ~spl6_23),
% 0.20/0.54    inference(resolution,[],[f67,f214])).
% 0.20/0.54  fof(f214,plain,(
% 0.20/0.54    v1_relat_1(sK4) | ~spl6_23),
% 0.20/0.54    inference(avatar_component_clause,[],[f212])).
% 0.20/0.54  fof(f583,plain,(
% 0.20/0.54    spl6_76 | ~spl6_31 | ~spl6_55),
% 0.20/0.54    inference(avatar_split_clause,[],[f578,f452,f263,f580])).
% 0.20/0.54  fof(f263,plain,(
% 0.20/0.54    spl6_31 <=> r1_xboole_0(sK2,sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.20/0.54  fof(f578,plain,(
% 0.20/0.54    k1_xboole_0 = k7_relat_1(sK5,sK2) | (~spl6_31 | ~spl6_55)),
% 0.20/0.54    inference(resolution,[],[f453,f265])).
% 0.20/0.54  fof(f265,plain,(
% 0.20/0.54    r1_xboole_0(sK2,sK3) | ~spl6_31),
% 0.20/0.54    inference(avatar_component_clause,[],[f263])).
% 0.20/0.54  fof(f567,plain,(
% 0.20/0.54    ~spl6_6 | ~spl6_12 | spl6_7 | ~spl6_13 | spl6_2 | spl6_73 | ~spl6_11 | ~spl6_50),
% 0.20/0.54    inference(avatar_split_clause,[],[f559,f423,f150,f565,f105,f160,f130,f155,f125])).
% 0.20/0.54  fof(f423,plain,(
% 0.20/0.54    spl6_50 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 0.20/0.54  fof(f559,plain,(
% 0.20/0.54    ( ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl6_11 | ~spl6_50)),
% 0.20/0.54    inference(resolution,[],[f424,f152])).
% 0.20/0.54  fof(f152,plain,(
% 0.20/0.54    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl6_11),
% 0.20/0.54    inference(avatar_component_clause,[],[f150])).
% 0.20/0.54  fof(f424,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl6_50),
% 0.20/0.54    inference(avatar_component_clause,[],[f423])).
% 0.20/0.54  fof(f545,plain,(
% 0.20/0.54    spl6_69 | ~spl6_31 | ~spl6_41),
% 0.20/0.54    inference(avatar_split_clause,[],[f540,f375,f263,f542])).
% 0.20/0.54  fof(f375,plain,(
% 0.20/0.54    spl6_41 <=> ! [X1] : (~r1_xboole_0(sK2,X1) | k1_xboole_0 = k9_relat_1(sK4,X1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.20/0.54  fof(f540,plain,(
% 0.20/0.54    k1_xboole_0 = k9_relat_1(sK4,sK3) | (~spl6_31 | ~spl6_41)),
% 0.20/0.54    inference(resolution,[],[f376,f265])).
% 0.20/0.54  fof(f376,plain,(
% 0.20/0.54    ( ! [X1] : (~r1_xboole_0(sK2,X1) | k1_xboole_0 = k9_relat_1(sK4,X1)) ) | ~spl6_41),
% 0.20/0.54    inference(avatar_component_clause,[],[f375])).
% 0.20/0.54  fof(f539,plain,(
% 0.20/0.54    ~spl6_6 | ~spl6_12 | spl6_7 | ~spl6_13 | spl6_2 | spl6_68 | ~spl6_11 | ~spl6_48),
% 0.20/0.54    inference(avatar_split_clause,[],[f531,f411,f150,f537,f105,f160,f130,f155,f125])).
% 0.20/0.54  fof(f411,plain,(
% 0.20/0.54    spl6_48 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 0.20/0.54  fof(f531,plain,(
% 0.20/0.54    ( ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl6_11 | ~spl6_48)),
% 0.20/0.54    inference(resolution,[],[f412,f152])).
% 0.20/0.54  fof(f412,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl6_48),
% 0.20/0.54    inference(avatar_component_clause,[],[f411])).
% 0.20/0.54  fof(f484,plain,(
% 0.20/0.54    spl6_25 | ~spl6_23 | ~spl6_57),
% 0.20/0.54    inference(avatar_split_clause,[],[f482,f463,f212,f225])).
% 0.20/0.54  fof(f482,plain,(
% 0.20/0.54    v1_relat_1(k1_xboole_0) | (~spl6_23 | ~spl6_57)),
% 0.20/0.54    inference(superposition,[],[f221,f465])).
% 0.20/0.54  fof(f221,plain,(
% 0.20/0.54    ( ! [X0] : (v1_relat_1(k7_relat_1(sK4,X0))) ) | ~spl6_23),
% 0.20/0.54    inference(resolution,[],[f214,f71])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.54  fof(f476,plain,(
% 0.20/0.54    ~spl6_6 | ~spl6_12 | spl6_7 | ~spl6_13 | spl6_2 | spl6_59 | ~spl6_11 | ~spl6_44),
% 0.20/0.54    inference(avatar_split_clause,[],[f468,f391,f150,f474,f105,f160,f130,f155,f125])).
% 0.20/0.54  fof(f391,plain,(
% 0.20/0.54    spl6_44 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.20/0.54  fof(f468,plain,(
% 0.20/0.54    ( ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl6_11 | ~spl6_44)),
% 0.20/0.54    inference(resolution,[],[f392,f152])).
% 0.20/0.54  fof(f392,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl6_44),
% 0.20/0.54    inference(avatar_component_clause,[],[f391])).
% 0.20/0.54  fof(f466,plain,(
% 0.20/0.54    spl6_57 | ~spl6_31 | ~spl6_40),
% 0.20/0.54    inference(avatar_split_clause,[],[f461,f371,f263,f463])).
% 0.20/0.54  fof(f371,plain,(
% 0.20/0.54    spl6_40 <=> ! [X0] : (~r1_xboole_0(sK2,X0) | k1_xboole_0 = k7_relat_1(sK4,X0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.20/0.54  fof(f461,plain,(
% 0.20/0.54    k1_xboole_0 = k7_relat_1(sK4,sK3) | (~spl6_31 | ~spl6_40)),
% 0.20/0.54    inference(resolution,[],[f372,f265])).
% 0.20/0.54  fof(f372,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_xboole_0(sK2,X0) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl6_40),
% 0.20/0.54    inference(avatar_component_clause,[],[f371])).
% 0.20/0.54  fof(f454,plain,(
% 0.20/0.54    ~spl6_24 | spl6_55 | ~spl6_36),
% 0.20/0.54    inference(avatar_split_clause,[],[f435,f343,f452,f217])).
% 0.20/0.54  fof(f435,plain,(
% 0.20/0.54    ( ! [X2] : (~r1_xboole_0(X2,sK3) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X2)) ) | ~spl6_36),
% 0.20/0.54    inference(superposition,[],[f66,f345])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 0.20/0.54  fof(f450,plain,(
% 0.20/0.54    ~spl6_24 | spl6_54 | ~spl6_36),
% 0.20/0.54    inference(avatar_split_clause,[],[f434,f343,f448,f217])).
% 0.20/0.54  fof(f434,plain,(
% 0.20/0.54    ( ! [X1] : (~r1_xboole_0(sK3,X1) | ~v1_relat_1(sK5) | k1_xboole_0 = k9_relat_1(sK5,X1)) ) | ~spl6_36),
% 0.20/0.54    inference(superposition,[],[f74,f345])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k1_xboole_0 = k9_relat_1(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f442,plain,(
% 0.20/0.54    spl6_52 | ~spl6_30 | ~spl6_36),
% 0.20/0.54    inference(avatar_split_clause,[],[f432,f343,f253,f439])).
% 0.20/0.54  fof(f253,plain,(
% 0.20/0.54    spl6_30 <=> r1_tarski(k1_relat_1(sK5),sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.20/0.54  fof(f432,plain,(
% 0.20/0.54    r1_tarski(sK3,sK3) | (~spl6_30 | ~spl6_36)),
% 0.20/0.54    inference(backward_demodulation,[],[f255,f345])).
% 0.20/0.54  fof(f255,plain,(
% 0.20/0.54    r1_tarski(k1_relat_1(sK5),sK3) | ~spl6_30),
% 0.20/0.54    inference(avatar_component_clause,[],[f253])).
% 0.20/0.54  fof(f425,plain,(
% 0.20/0.54    spl6_1 | spl6_4 | spl6_50 | ~spl6_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f418,f110,f423,f115,f100])).
% 0.20/0.54  fof(f418,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0)))) ) | ~spl6_3),
% 0.20/0.54    inference(resolution,[],[f90,f112])).
% 0.20/0.54  fof(f112,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl6_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f110])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 0.20/0.54  fof(f413,plain,(
% 0.20/0.54    spl6_1 | spl6_4 | spl6_48 | ~spl6_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f406,f110,f411,f115,f100])).
% 0.20/0.54  fof(f406,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0)) ) | ~spl6_3),
% 0.20/0.54    inference(resolution,[],[f89,f112])).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f46])).
% 0.20/0.54  fof(f393,plain,(
% 0.20/0.54    spl6_1 | spl6_4 | spl6_44 | ~spl6_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f386,f110,f391,f115,f100])).
% 0.20/0.54  fof(f386,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3))) ) | ~spl6_3),
% 0.20/0.54    inference(resolution,[],[f88,f112])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f46])).
% 0.20/0.54  fof(f381,plain,(
% 0.20/0.54    ~spl6_23 | spl6_42 | ~spl6_35),
% 0.20/0.54    inference(avatar_split_clause,[],[f362,f337,f379,f212])).
% 0.20/0.54  fof(f337,plain,(
% 0.20/0.54    spl6_35 <=> sK2 = k1_relat_1(sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.20/0.54  fof(f362,plain,(
% 0.20/0.54    ( ! [X2] : (~r1_xboole_0(X2,sK2) | ~v1_relat_1(sK4) | k1_xboole_0 = k7_relat_1(sK4,X2)) ) | ~spl6_35),
% 0.20/0.54    inference(superposition,[],[f66,f339])).
% 0.20/0.54  fof(f339,plain,(
% 0.20/0.54    sK2 = k1_relat_1(sK4) | ~spl6_35),
% 0.20/0.54    inference(avatar_component_clause,[],[f337])).
% 0.20/0.54  fof(f377,plain,(
% 0.20/0.54    ~spl6_23 | spl6_41 | ~spl6_35),
% 0.20/0.54    inference(avatar_split_clause,[],[f361,f337,f375,f212])).
% 0.20/0.54  fof(f361,plain,(
% 0.20/0.54    ( ! [X1] : (~r1_xboole_0(sK2,X1) | ~v1_relat_1(sK4) | k1_xboole_0 = k9_relat_1(sK4,X1)) ) | ~spl6_35),
% 0.20/0.54    inference(superposition,[],[f74,f339])).
% 0.20/0.54  fof(f373,plain,(
% 0.20/0.54    ~spl6_23 | spl6_40 | ~spl6_35),
% 0.20/0.54    inference(avatar_split_clause,[],[f360,f337,f371,f212])).
% 0.20/0.54  fof(f360,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_xboole_0(sK2,X0) | ~v1_relat_1(sK4) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl6_35),
% 0.20/0.54    inference(superposition,[],[f76,f339])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f369,plain,(
% 0.20/0.54    spl6_39 | ~spl6_29 | ~spl6_35),
% 0.20/0.54    inference(avatar_split_clause,[],[f359,f337,f247,f366])).
% 0.20/0.54  fof(f247,plain,(
% 0.20/0.54    spl6_29 <=> r1_tarski(k1_relat_1(sK4),sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.20/0.54  fof(f359,plain,(
% 0.20/0.54    r1_tarski(sK2,sK2) | (~spl6_29 | ~spl6_35)),
% 0.20/0.54    inference(backward_demodulation,[],[f249,f339])).
% 0.20/0.54  fof(f249,plain,(
% 0.20/0.54    r1_tarski(k1_relat_1(sK4),sK2) | ~spl6_29),
% 0.20/0.54    inference(avatar_component_clause,[],[f247])).
% 0.20/0.54  fof(f356,plain,(
% 0.20/0.54    spl6_38 | ~spl6_13 | ~spl6_11),
% 0.20/0.54    inference(avatar_split_clause,[],[f348,f150,f160,f354])).
% 0.20/0.54  fof(f348,plain,(
% 0.20/0.54    ( ! [X1] : (~v1_funct_1(sK5) | k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl6_11),
% 0.20/0.54    inference(resolution,[],[f87,f152])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.54    inference(flattening,[],[f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.54  fof(f352,plain,(
% 0.20/0.54    spl6_37 | ~spl6_10 | ~spl6_8),
% 0.20/0.54    inference(avatar_split_clause,[],[f347,f135,f145,f350])).
% 0.20/0.54  fof(f347,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_funct_1(sK4) | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl6_8),
% 0.20/0.54    inference(resolution,[],[f87,f137])).
% 0.20/0.54  fof(f346,plain,(
% 0.20/0.54    ~spl6_24 | spl6_36 | ~spl6_28 | ~spl6_34),
% 0.20/0.54    inference(avatar_split_clause,[],[f341,f331,f241,f343,f217])).
% 0.20/0.56  % (4115)Refutation not found, incomplete strategy% (4115)------------------------------
% 0.20/0.56  % (4115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  fof(f241,plain,(
% 0.20/0.56    spl6_28 <=> v4_relat_1(sK5,sK3)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.20/0.56  fof(f331,plain,(
% 0.20/0.56    spl6_34 <=> v1_partfun1(sK5,sK3)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.20/0.56  fof(f341,plain,(
% 0.20/0.56    ~v4_relat_1(sK5,sK3) | sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5) | ~spl6_34),
% 0.20/0.56    inference(resolution,[],[f333,f81])).
% 0.20/0.56  fof(f81,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f39])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(flattening,[],[f38])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.56    inference(ennf_transformation,[],[f16])).
% 0.20/0.56  fof(f16,axiom,(
% 0.20/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.56  fof(f333,plain,(
% 0.20/0.56    v1_partfun1(sK5,sK3) | ~spl6_34),
% 0.20/0.56    inference(avatar_component_clause,[],[f331])).
% 0.20/0.56  fof(f340,plain,(
% 0.20/0.56    ~spl6_23 | spl6_35 | ~spl6_27 | ~spl6_33),
% 0.20/0.56    inference(avatar_split_clause,[],[f335,f326,f236,f337,f212])).
% 0.20/0.56  fof(f236,plain,(
% 0.20/0.56    spl6_27 <=> v4_relat_1(sK4,sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.20/0.56  fof(f326,plain,(
% 0.20/0.56    spl6_33 <=> v1_partfun1(sK4,sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.20/0.56  fof(f335,plain,(
% 0.20/0.56    ~v4_relat_1(sK4,sK2) | sK2 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl6_33),
% 0.20/0.56    inference(resolution,[],[f328,f81])).
% 0.20/0.56  fof(f328,plain,(
% 0.20/0.56    v1_partfun1(sK4,sK2) | ~spl6_33),
% 0.20/0.56    inference(avatar_component_clause,[],[f326])).
% 0.20/0.56  fof(f334,plain,(
% 0.20/0.56    spl6_34 | ~spl6_12 | ~spl6_13 | spl6_2 | ~spl6_11),
% 0.20/0.56    inference(avatar_split_clause,[],[f324,f150,f105,f160,f155,f331])).
% 0.20/0.56  fof(f324,plain,(
% 0.20/0.56    v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3) | ~spl6_11),
% 0.20/0.56    inference(resolution,[],[f70,f152])).
% 0.20/0.56  fof(f70,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f31])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.56    inference(flattening,[],[f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,axiom,(
% 0.20/0.56    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.56  fof(f329,plain,(
% 0.20/0.56    spl6_33 | ~spl6_9 | ~spl6_10 | spl6_2 | ~spl6_8),
% 0.20/0.56    inference(avatar_split_clause,[],[f323,f135,f105,f145,f140,f326])).
% 0.20/0.56  fof(f323,plain,(
% 0.20/0.56    v1_xboole_0(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2) | ~spl6_8),
% 0.20/0.56    inference(resolution,[],[f70,f137])).
% 0.20/0.56  fof(f273,plain,(
% 0.20/0.56    spl6_32 | ~spl6_31),
% 0.20/0.56    inference(avatar_split_clause,[],[f268,f263,f270])).
% 0.20/0.56  fof(f268,plain,(
% 0.20/0.56    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl6_31),
% 0.20/0.56    inference(resolution,[],[f265,f91])).
% 0.20/0.56  fof(f91,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.56    inference(definition_unfolding,[],[f83,f69])).
% 0.20/0.56  fof(f83,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.56  fof(f266,plain,(
% 0.20/0.56    spl6_4 | spl6_31 | spl6_7 | ~spl6_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f261,f120,f130,f263,f115])).
% 0.20/0.56  fof(f120,plain,(
% 0.20/0.56    spl6_5 <=> r1_subset_1(sK2,sK3)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.56  fof(f261,plain,(
% 0.20/0.56    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | ~spl6_5),
% 0.20/0.56    inference(resolution,[],[f79,f122])).
% 0.20/0.56  fof(f122,plain,(
% 0.20/0.56    r1_subset_1(sK2,sK3) | ~spl6_5),
% 0.20/0.56    inference(avatar_component_clause,[],[f120])).
% 0.20/0.56  fof(f79,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.56    inference(flattening,[],[f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f12])).
% 0.20/0.56  fof(f12,axiom,(
% 0.20/0.56    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 0.20/0.56  fof(f256,plain,(
% 0.20/0.56    ~spl6_24 | spl6_30 | ~spl6_28),
% 0.20/0.56    inference(avatar_split_clause,[],[f251,f241,f253,f217])).
% 0.20/0.56  fof(f251,plain,(
% 0.20/0.56    r1_tarski(k1_relat_1(sK5),sK3) | ~v1_relat_1(sK5) | ~spl6_28),
% 0.20/0.56    inference(resolution,[],[f243,f73])).
% 0.20/0.56  fof(f73,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.56  fof(f243,plain,(
% 0.20/0.56    v4_relat_1(sK5,sK3) | ~spl6_28),
% 0.20/0.56    inference(avatar_component_clause,[],[f241])).
% 0.20/0.56  fof(f250,plain,(
% 0.20/0.56    ~spl6_23 | spl6_29 | ~spl6_27),
% 0.20/0.56    inference(avatar_split_clause,[],[f245,f236,f247,f212])).
% 0.20/0.56  fof(f245,plain,(
% 0.20/0.56    r1_tarski(k1_relat_1(sK4),sK2) | ~v1_relat_1(sK4) | ~spl6_27),
% 0.20/0.56    inference(resolution,[],[f238,f73])).
% 0.20/0.56  fof(f238,plain,(
% 0.20/0.56    v4_relat_1(sK4,sK2) | ~spl6_27),
% 0.20/0.56    inference(avatar_component_clause,[],[f236])).
% 0.20/0.56  fof(f244,plain,(
% 0.20/0.56    spl6_28 | ~spl6_11),
% 0.20/0.56    inference(avatar_split_clause,[],[f234,f150,f241])).
% 0.20/0.56  fof(f234,plain,(
% 0.20/0.56    v4_relat_1(sK5,sK3) | ~spl6_11),
% 0.20/0.56    inference(resolution,[],[f86,f152])).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f42])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(ennf_transformation,[],[f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.56    inference(pure_predicate_removal,[],[f14])).
% 0.20/0.56  fof(f14,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.56  fof(f239,plain,(
% 0.20/0.56    spl6_27 | ~spl6_8),
% 0.20/0.56    inference(avatar_split_clause,[],[f233,f135,f236])).
% 0.20/0.56  fof(f233,plain,(
% 0.20/0.56    v4_relat_1(sK4,sK2) | ~spl6_8),
% 0.20/0.56    inference(resolution,[],[f86,f137])).
% 0.20/0.56  fof(f220,plain,(
% 0.20/0.56    spl6_24 | ~spl6_11),
% 0.20/0.56    inference(avatar_split_clause,[],[f210,f150,f217])).
% 0.20/0.56  fof(f210,plain,(
% 0.20/0.56    v1_relat_1(sK5) | ~spl6_11),
% 0.20/0.56    inference(resolution,[],[f85,f152])).
% 0.20/0.56  fof(f85,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f41])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(ennf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.56  fof(f215,plain,(
% 0.20/0.56    spl6_23 | ~spl6_8),
% 0.20/0.56    inference(avatar_split_clause,[],[f209,f135,f212])).
% 0.20/0.56  fof(f209,plain,(
% 0.20/0.56    v1_relat_1(sK4) | ~spl6_8),
% 0.20/0.56    inference(resolution,[],[f85,f137])).
% 0.20/0.56  fof(f186,plain,(
% 0.20/0.56    spl6_18),
% 0.20/0.56    inference(avatar_split_clause,[],[f61,f183])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.56    inference(cnf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,axiom,(
% 0.20/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.56  fof(f176,plain,(
% 0.20/0.56    ~spl6_14 | ~spl6_15 | ~spl6_16),
% 0.20/0.56    inference(avatar_split_clause,[],[f47,f173,f169,f165])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.56    inference(flattening,[],[f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f21])).
% 0.20/0.56  fof(f21,negated_conjecture,(
% 0.20/0.56    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.20/0.56    inference(negated_conjecture,[],[f20])).
% 0.20/0.56  fof(f20,conjecture,(
% 0.20/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).
% 0.20/0.56  fof(f163,plain,(
% 0.20/0.56    spl6_13),
% 0.20/0.56    inference(avatar_split_clause,[],[f48,f160])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    v1_funct_1(sK5)),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f158,plain,(
% 0.20/0.56    spl6_12),
% 0.20/0.56    inference(avatar_split_clause,[],[f49,f155])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    v1_funct_2(sK5,sK3,sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f153,plain,(
% 0.20/0.56    spl6_11),
% 0.20/0.56    inference(avatar_split_clause,[],[f50,f150])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f148,plain,(
% 0.20/0.56    spl6_10),
% 0.20/0.56    inference(avatar_split_clause,[],[f51,f145])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    v1_funct_1(sK4)),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f143,plain,(
% 0.20/0.56    spl6_9),
% 0.20/0.56    inference(avatar_split_clause,[],[f52,f140])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    v1_funct_2(sK4,sK2,sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f138,plain,(
% 0.20/0.56    spl6_8),
% 0.20/0.56    inference(avatar_split_clause,[],[f53,f135])).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f133,plain,(
% 0.20/0.56    ~spl6_7),
% 0.20/0.56    inference(avatar_split_clause,[],[f54,f130])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ~v1_xboole_0(sK3)),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f128,plain,(
% 0.20/0.56    spl6_6),
% 0.20/0.56    inference(avatar_split_clause,[],[f55,f125])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f123,plain,(
% 0.20/0.56    spl6_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f56,f120])).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    r1_subset_1(sK2,sK3)),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f118,plain,(
% 0.20/0.56    ~spl6_4),
% 0.20/0.56    inference(avatar_split_clause,[],[f57,f115])).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    ~v1_xboole_0(sK2)),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f113,plain,(
% 0.20/0.56    spl6_3),
% 0.20/0.56    inference(avatar_split_clause,[],[f58,f110])).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f108,plain,(
% 0.20/0.56    ~spl6_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f59,f105])).
% 0.20/0.56  fof(f59,plain,(
% 0.20/0.56    ~v1_xboole_0(sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f103,plain,(
% 0.20/0.56    ~spl6_1),
% 0.20/0.56    inference(avatar_split_clause,[],[f60,f100])).
% 0.20/0.56  fof(f60,plain,(
% 0.20/0.56    ~v1_xboole_0(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (4109)------------------------------
% 0.20/0.56  % (4109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (4109)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (4109)Memory used [KB]: 11769
% 0.20/0.56  % (4109)Time elapsed: 0.137 s
% 0.20/0.56  % (4109)------------------------------
% 0.20/0.56  % (4109)------------------------------
% 0.20/0.56  % (4092)Success in time 0.202 s
%------------------------------------------------------------------------------
