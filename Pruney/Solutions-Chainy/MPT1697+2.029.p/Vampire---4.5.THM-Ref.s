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
% DateTime   : Thu Dec  3 13:17:31 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  259 ( 582 expanded)
%              Number of leaves         :   61 ( 280 expanded)
%              Depth                    :   14
%              Number of atoms          : 1352 (2937 expanded)
%              Number of equality atoms :  149 ( 407 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1013,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f173,f202,f207,f219,f226,f231,f239,f269,f277,f282,f315,f327,f331,f337,f352,f371,f379,f399,f438,f461,f491,f543,f563,f570,f645,f657,f681,f842,f894,f902,f1012])).

fof(f1012,plain,
    ( ~ spl6_60
    | ~ spl6_6
    | spl6_16
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_85
    | ~ spl6_95 ),
    inference(avatar_split_clause,[],[f1011,f642,f567,f329,f325,f170,f122,f435])).

fof(f435,plain,
    ( spl6_60
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f122,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f170,plain,
    ( spl6_16
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f325,plain,
    ( spl6_40
  <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f329,plain,
    ( spl6_41
  <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f567,plain,
    ( spl6_85
  <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f642,plain,
    ( spl6_95
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).

fof(f1011,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_6
    | spl6_16
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_85
    | ~ spl6_95 ),
    inference(forward_demodulation,[],[f1010,f569])).

fof(f569,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_85 ),
    inference(avatar_component_clause,[],[f567])).

fof(f1010,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_6
    | spl6_16
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_95 ),
    inference(forward_demodulation,[],[f1009,f326])).

fof(f326,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f325])).

fof(f1009,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl6_6
    | spl6_16
    | ~ spl6_41
    | ~ spl6_95 ),
    inference(forward_demodulation,[],[f1008,f644])).

fof(f644,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl6_95 ),
    inference(avatar_component_clause,[],[f642])).

fof(f1008,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl6_6
    | spl6_16
    | ~ spl6_41 ),
    inference(forward_demodulation,[],[f1007,f293])).

fof(f293,plain,
    ( ! [X1] : k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))
    | ~ spl6_6 ),
    inference(resolution,[],[f90,f124])).

fof(f124,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f82,f71])).

fof(f71,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f82,plain,(
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

fof(f1007,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_16
    | ~ spl6_41 ),
    inference(forward_demodulation,[],[f172,f330])).

fof(f330,plain,
    ( ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f329])).

fof(f172,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f170])).

fof(f902,plain,
    ( spl6_14
    | spl6_1
    | ~ spl6_101
    | ~ spl6_97
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
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_60
    | ~ spl6_85
    | ~ spl6_95
    | ~ spl6_131 ),
    inference(avatar_split_clause,[],[f901,f839,f642,f567,f435,f329,f325,f122,f102,f112,f107,f127,f122,f142,f137,f132,f157,f152,f147,f654,f678,f97,f162])).

fof(f162,plain,
    ( spl6_14
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f97,plain,
    ( spl6_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f678,plain,
    ( spl6_101
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).

fof(f654,plain,
    ( spl6_97
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f147,plain,
    ( spl6_11
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f152,plain,
    ( spl6_12
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f157,plain,
    ( spl6_13
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f132,plain,
    ( spl6_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f137,plain,
    ( spl6_9
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f142,plain,
    ( spl6_10
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f127,plain,
    ( spl6_7
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f107,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f112,plain,
    ( spl6_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f102,plain,
    ( spl6_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f839,plain,
    ( spl6_131
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_131])])).

fof(f901,plain,
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
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_60
    | ~ spl6_85
    | ~ spl6_95
    | ~ spl6_131 ),
    inference(trivial_inequality_removal,[],[f900])).

fof(f900,plain,
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
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_60
    | ~ spl6_85
    | ~ spl6_95
    | ~ spl6_131 ),
    inference(forward_demodulation,[],[f899,f437])).

fof(f437,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f435])).

fof(f899,plain,
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
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_85
    | ~ spl6_95
    | ~ spl6_131 ),
    inference(forward_demodulation,[],[f898,f569])).

fof(f898,plain,
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
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_95
    | ~ spl6_131 ),
    inference(forward_demodulation,[],[f897,f326])).

fof(f897,plain,
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
    | ~ spl6_41
    | ~ spl6_95
    | ~ spl6_131 ),
    inference(forward_demodulation,[],[f896,f644])).

fof(f896,plain,
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
    | ~ spl6_41
    | ~ spl6_131 ),
    inference(forward_demodulation,[],[f895,f293])).

fof(f895,plain,
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
    | ~ spl6_41
    | ~ spl6_131 ),
    inference(forward_demodulation,[],[f865,f330])).

fof(f865,plain,
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
    | ~ spl6_131 ),
    inference(resolution,[],[f841,f93])).

fof(f93,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).

fof(f841,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_131 ),
    inference(avatar_component_clause,[],[f839])).

fof(f894,plain,
    ( spl6_15
    | spl6_1
    | ~ spl6_101
    | ~ spl6_97
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
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_60
    | ~ spl6_85
    | ~ spl6_95
    | ~ spl6_131 ),
    inference(avatar_split_clause,[],[f893,f839,f642,f567,f435,f329,f325,f122,f102,f112,f107,f127,f122,f142,f137,f132,f157,f152,f147,f654,f678,f97,f166])).

fof(f166,plain,
    ( spl6_15
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f893,plain,
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
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_60
    | ~ spl6_85
    | ~ spl6_95
    | ~ spl6_131 ),
    inference(trivial_inequality_removal,[],[f892])).

fof(f892,plain,
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
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_60
    | ~ spl6_85
    | ~ spl6_95
    | ~ spl6_131 ),
    inference(forward_demodulation,[],[f891,f437])).

fof(f891,plain,
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
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_85
    | ~ spl6_95
    | ~ spl6_131 ),
    inference(forward_demodulation,[],[f890,f569])).

fof(f890,plain,
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
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_95
    | ~ spl6_131 ),
    inference(forward_demodulation,[],[f889,f326])).

fof(f889,plain,
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
    | ~ spl6_41
    | ~ spl6_95
    | ~ spl6_131 ),
    inference(forward_demodulation,[],[f888,f644])).

fof(f888,plain,
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
    | ~ spl6_41
    | ~ spl6_131 ),
    inference(forward_demodulation,[],[f887,f293])).

fof(f887,plain,
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
    | ~ spl6_41
    | ~ spl6_131 ),
    inference(forward_demodulation,[],[f864,f330])).

fof(f864,plain,
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
    | ~ spl6_131 ),
    inference(resolution,[],[f841,f94])).

fof(f94,plain,(
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
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f842,plain,
    ( spl6_131
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f837,f561,f132,f137,f142,f839])).

fof(f561,plain,
    ( spl6_84
  <=> ! [X1] :
        ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f837,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_8
    | ~ spl6_84 ),
    inference(resolution,[],[f562,f134])).

fof(f134,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f132])).

fof(f562,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) )
    | ~ spl6_84 ),
    inference(avatar_component_clause,[],[f561])).

fof(f681,plain,
    ( spl6_101
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f676,f541,f132,f137,f142,f678])).

fof(f541,plain,
    ( spl6_80
  <=> ! [X1] :
        ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f676,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_8
    | ~ spl6_80 ),
    inference(resolution,[],[f542,f134])).

fof(f542,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) )
    | ~ spl6_80 ),
    inference(avatar_component_clause,[],[f541])).

fof(f657,plain,
    ( spl6_97
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_64 ),
    inference(avatar_split_clause,[],[f652,f459,f132,f137,f142,f654])).

fof(f459,plain,
    ( spl6_64
  <=> ! [X1] :
        ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f652,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_8
    | ~ spl6_64 ),
    inference(resolution,[],[f460,f134])).

fof(f460,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) )
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f459])).

fof(f645,plain,
    ( spl6_95
    | ~ spl6_22
    | ~ spl6_48
    | ~ spl6_69 ),
    inference(avatar_split_clause,[],[f640,f488,f368,f204,f642])).

fof(f204,plain,
    ( spl6_22
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f368,plain,
    ( spl6_48
  <=> sK3 = k10_relat_1(sK5,k2_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f488,plain,
    ( spl6_69
  <=> k1_xboole_0 = k7_relat_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f640,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl6_22
    | ~ spl6_48
    | ~ spl6_69 ),
    inference(forward_demodulation,[],[f632,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(f632,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK3)) = k10_relat_1(k1_xboole_0,k2_relat_1(sK5))
    | ~ spl6_22
    | ~ spl6_48
    | ~ spl6_69 ),
    inference(superposition,[],[f624,f490])).

fof(f490,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl6_69 ),
    inference(avatar_component_clause,[],[f488])).

fof(f624,plain,
    ( ! [X0] : k1_setfam_1(k2_tarski(X0,sK3)) = k10_relat_1(k7_relat_1(sK5,X0),k2_relat_1(sK5))
    | ~ spl6_22
    | ~ spl6_48 ),
    inference(superposition,[],[f303,f370])).

fof(f370,plain,
    ( sK3 = k10_relat_1(sK5,k2_relat_1(sK5))
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f368])).

fof(f303,plain,
    ( ! [X2,X3] : k10_relat_1(k7_relat_1(sK5,X2),X3) = k1_setfam_1(k2_tarski(X2,k10_relat_1(sK5,X3)))
    | ~ spl6_22 ),
    inference(resolution,[],[f89,f206])).

fof(f206,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f204])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f80,f71])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f570,plain,
    ( spl6_85
    | ~ spl6_22
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f564,f279,f204,f567])).

fof(f279,plain,
    ( spl6_34
  <=> sK5 = k7_relat_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f564,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_22
    | ~ spl6_34 ),
    inference(superposition,[],[f478,f281])).

fof(f281,plain,
    ( sK5 = k7_relat_1(sK5,sK3)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f279])).

fof(f478,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k7_relat_1(sK5,X0),k1_xboole_0)
    | ~ spl6_22 ),
    inference(resolution,[],[f285,f64])).

fof(f64,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f285,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(X2,X3)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(sK5,X2),X3) )
    | ~ spl6_22 ),
    inference(resolution,[],[f81,f206])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f563,plain,
    ( ~ spl6_6
    | ~ spl6_12
    | spl6_7
    | ~ spl6_13
    | spl6_2
    | spl6_84
    | ~ spl6_11
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f555,f397,f147,f561,f102,f157,f127,f152,f122])).

fof(f397,plain,
    ( spl6_53
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f555,plain,
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
    | ~ spl6_53 ),
    inference(resolution,[],[f398,f149])).

fof(f149,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f147])).

fof(f398,plain,
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
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f397])).

fof(f543,plain,
    ( ~ spl6_6
    | ~ spl6_12
    | spl6_7
    | ~ spl6_13
    | spl6_2
    | spl6_80
    | ~ spl6_11
    | ~ spl6_49 ),
    inference(avatar_split_clause,[],[f535,f377,f147,f541,f102,f157,f127,f152,f122])).

fof(f377,plain,
    ( spl6_49
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f535,plain,
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
    | ~ spl6_49 ),
    inference(resolution,[],[f378,f149])).

fof(f378,plain,
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
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f377])).

fof(f491,plain,
    ( spl6_69
    | ~ spl6_22
    | ~ spl6_32
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f486,f279,f266,f204,f488])).

fof(f266,plain,
    ( spl6_32
  <=> r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f486,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl6_22
    | ~ spl6_32
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f480,f281])).

fof(f480,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK5,sK3),sK2)
    | ~ spl6_22
    | ~ spl6_32 ),
    inference(resolution,[],[f285,f268])).

fof(f268,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f266])).

fof(f461,plain,
    ( ~ spl6_6
    | ~ spl6_12
    | spl6_7
    | ~ spl6_13
    | spl6_2
    | spl6_64
    | ~ spl6_11
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f453,f350,f147,f459,f102,f157,f127,f152,f122])).

fof(f350,plain,
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

fof(f453,plain,
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
    inference(resolution,[],[f351,f149])).

fof(f351,plain,
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
    inference(avatar_component_clause,[],[f350])).

fof(f438,plain,
    ( spl6_60
    | ~ spl6_21
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f432,f274,f199,f435])).

fof(f199,plain,
    ( spl6_21
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f274,plain,
    ( spl6_33
  <=> sK4 = k7_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f432,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_21
    | ~ spl6_33 ),
    inference(superposition,[],[f412,f276])).

fof(f276,plain,
    ( sK4 = k7_relat_1(sK4,sK2)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f274])).

fof(f412,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,X0),k1_xboole_0)
    | ~ spl6_21 ),
    inference(resolution,[],[f284,f64])).

fof(f284,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,X0),X1) )
    | ~ spl6_21 ),
    inference(resolution,[],[f81,f201])).

fof(f201,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f199])).

fof(f399,plain,
    ( spl6_1
    | spl6_4
    | spl6_53
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f392,f107,f397,f112,f97])).

fof(f392,plain,
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
    inference(resolution,[],[f88,f109])).

fof(f109,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f107])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(f379,plain,
    ( spl6_1
    | spl6_4
    | spl6_49
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f372,f107,f377,f112,f97])).

fof(f372,plain,
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
    inference(resolution,[],[f87,f109])).

fof(f87,plain,(
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

fof(f371,plain,
    ( spl6_48
    | ~ spl6_24
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f365,f334,f216,f368])).

fof(f216,plain,
    ( spl6_24
  <=> k10_relat_1(sK5,k2_relat_1(sK5)) = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f334,plain,
    ( spl6_42
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f365,plain,
    ( sK3 = k10_relat_1(sK5,k2_relat_1(sK5))
    | ~ spl6_24
    | ~ spl6_42 ),
    inference(backward_demodulation,[],[f218,f336])).

fof(f336,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f334])).

fof(f218,plain,
    ( k10_relat_1(sK5,k2_relat_1(sK5)) = k1_relat_1(sK5)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f216])).

fof(f352,plain,
    ( spl6_1
    | spl6_4
    | spl6_44
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f345,f107,f350,f112,f97])).

fof(f345,plain,
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
    inference(resolution,[],[f86,f109])).

fof(f86,plain,(
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

fof(f337,plain,
    ( ~ spl6_22
    | spl6_42
    | ~ spl6_26
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f332,f312,f228,f334,f204])).

fof(f228,plain,
    ( spl6_26
  <=> v4_relat_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f312,plain,
    ( spl6_38
  <=> v1_partfun1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f332,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl6_38 ),
    inference(resolution,[],[f314,f79])).

fof(f79,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f314,plain,
    ( v1_partfun1(sK5,sK3)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f312])).

fof(f331,plain,
    ( spl6_41
    | ~ spl6_13
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f323,f147,f157,f329])).

fof(f323,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK5)
        | k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1) )
    | ~ spl6_11 ),
    inference(resolution,[],[f85,f149])).

fof(f85,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f327,plain,
    ( spl6_40
    | ~ spl6_10
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f322,f132,f142,f325])).

fof(f322,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) )
    | ~ spl6_8 ),
    inference(resolution,[],[f85,f134])).

fof(f315,plain,
    ( spl6_38
    | ~ spl6_12
    | ~ spl6_13
    | spl6_2
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f305,f147,f102,f157,f152,f312])).

fof(f305,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f72,f149])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f282,plain,
    ( spl6_34
    | ~ spl6_22
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f272,f228,f204,f279])).

fof(f272,plain,
    ( ~ v1_relat_1(sK5)
    | sK5 = k7_relat_1(sK5,sK3)
    | ~ spl6_26 ),
    inference(resolution,[],[f77,f230])).

fof(f230,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f228])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f277,plain,
    ( spl6_33
    | ~ spl6_21
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f271,f223,f199,f274])).

fof(f223,plain,
    ( spl6_25
  <=> v4_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f271,plain,
    ( ~ v1_relat_1(sK4)
    | sK4 = k7_relat_1(sK4,sK2)
    | ~ spl6_25 ),
    inference(resolution,[],[f77,f225])).

fof(f225,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f223])).

fof(f269,plain,
    ( spl6_7
    | spl6_32
    | spl6_4
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f257,f236,f112,f266,f127])).

fof(f236,plain,
    ( spl6_27
  <=> r1_subset_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f257,plain,
    ( v1_xboole_0(sK2)
    | r1_xboole_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | ~ spl6_27 ),
    inference(resolution,[],[f76,f238])).

fof(f238,plain,
    ( r1_subset_1(sK3,sK2)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f236])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f239,plain,
    ( spl6_27
    | spl6_4
    | spl6_7
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f234,f117,f127,f112,f236])).

fof(f117,plain,
    ( spl6_5
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f234,plain,
    ( v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | r1_subset_1(sK3,sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f74,f119])).

fof(f119,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | r1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
       => r1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

fof(f231,plain,
    ( spl6_26
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f221,f147,f228])).

fof(f221,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f84,f149])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f226,plain,
    ( spl6_25
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f220,f132,f223])).

fof(f220,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f84,f134])).

fof(f219,plain,
    ( spl6_24
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f214,f204,f216])).

fof(f214,plain,
    ( k10_relat_1(sK5,k2_relat_1(sK5)) = k1_relat_1(sK5)
    | ~ spl6_22 ),
    inference(resolution,[],[f206,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f207,plain,
    ( spl6_22
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f197,f147,f204])).

fof(f197,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_11 ),
    inference(resolution,[],[f83,f149])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f202,plain,
    ( spl6_21
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f196,f132,f199])).

fof(f196,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_8 ),
    inference(resolution,[],[f83,f134])).

fof(f173,plain,
    ( ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f50,f170,f166,f162])).

fof(f50,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).

fof(f160,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f51,f157])).

fof(f51,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f155,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f52,f152])).

fof(f52,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f150,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f53,f147])).

fof(f53,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f145,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f54,f142])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f140,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f55,f137])).

fof(f55,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f135,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f56,f132])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f130,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f57,f127])).

fof(f57,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f125,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f58,f122])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f120,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f59,f117])).

fof(f59,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f115,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f60,f112])).

fof(f60,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f110,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f61,f107])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f105,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f62,f102])).

fof(f62,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f100,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f63,f97])).

fof(f63,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:01:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (31554)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.22/0.52  % (31546)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.22/0.52  % (31539)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.22/0.53  % (31542)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.22/0.53  % (31557)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.22/0.53  % (31533)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.22/0.53  % (31537)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.22/0.53  % (31560)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.54  % (31531)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.54  % (31545)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.34/0.54  % (31535)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.55  % (31532)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.34/0.55  % (31553)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.34/0.55  % (31543)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.55  % (31550)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.55  % (31555)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.34/0.55  % (31534)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.55  % (31544)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.34/0.55  % (31540)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.34/0.56  % (31559)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.56  % (31549)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.56  % (31551)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.34/0.56  % (31547)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.57  % (31548)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.57  % (31548)Refutation not found, incomplete strategy% (31548)------------------------------
% 1.34/0.57  % (31548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.57  % (31548)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.57  
% 1.34/0.57  % (31548)Memory used [KB]: 10746
% 1.34/0.57  % (31548)Time elapsed: 0.149 s
% 1.34/0.57  % (31548)------------------------------
% 1.34/0.57  % (31548)------------------------------
% 1.34/0.57  % (31558)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.58  % (31536)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.34/0.58  % (31541)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.34/0.59  % (31556)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.59  % (31538)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.34/0.60  % (31552)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.34/0.60  % (31553)Refutation not found, incomplete strategy% (31553)------------------------------
% 1.34/0.60  % (31553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.60  % (31553)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.60  
% 1.34/0.60  % (31553)Memory used [KB]: 11513
% 1.34/0.60  % (31553)Time elapsed: 0.164 s
% 1.34/0.60  % (31553)------------------------------
% 1.34/0.60  % (31553)------------------------------
% 1.34/0.62  % (31547)Refutation found. Thanks to Tanya!
% 1.34/0.62  % SZS status Theorem for theBenchmark
% 1.34/0.62  % SZS output start Proof for theBenchmark
% 1.34/0.62  fof(f1013,plain,(
% 1.34/0.62    $false),
% 1.34/0.62    inference(avatar_sat_refutation,[],[f100,f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f173,f202,f207,f219,f226,f231,f239,f269,f277,f282,f315,f327,f331,f337,f352,f371,f379,f399,f438,f461,f491,f543,f563,f570,f645,f657,f681,f842,f894,f902,f1012])).
% 1.34/0.62  fof(f1012,plain,(
% 1.34/0.62    ~spl6_60 | ~spl6_6 | spl6_16 | ~spl6_40 | ~spl6_41 | ~spl6_85 | ~spl6_95),
% 1.34/0.62    inference(avatar_split_clause,[],[f1011,f642,f567,f329,f325,f170,f122,f435])).
% 1.34/0.62  fof(f435,plain,(
% 1.34/0.62    spl6_60 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 1.34/0.62  fof(f122,plain,(
% 1.34/0.62    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.34/0.62  fof(f170,plain,(
% 1.34/0.62    spl6_16 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.34/0.62  fof(f325,plain,(
% 1.34/0.62    spl6_40 <=> ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 1.34/0.62  fof(f329,plain,(
% 1.34/0.62    spl6_41 <=> ! [X1] : k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 1.34/0.62  fof(f567,plain,(
% 1.34/0.62    spl6_85 <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).
% 1.34/0.62  fof(f642,plain,(
% 1.34/0.62    spl6_95 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).
% 1.34/0.62  fof(f1011,plain,(
% 1.34/0.62    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | (~spl6_6 | spl6_16 | ~spl6_40 | ~spl6_41 | ~spl6_85 | ~spl6_95)),
% 1.34/0.62    inference(forward_demodulation,[],[f1010,f569])).
% 1.34/0.62  fof(f569,plain,(
% 1.34/0.62    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | ~spl6_85),
% 1.34/0.62    inference(avatar_component_clause,[],[f567])).
% 1.34/0.62  fof(f1010,plain,(
% 1.34/0.62    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | (~spl6_6 | spl6_16 | ~spl6_40 | ~spl6_41 | ~spl6_95)),
% 1.34/0.62    inference(forward_demodulation,[],[f1009,f326])).
% 1.34/0.62  fof(f326,plain,(
% 1.34/0.62    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl6_40),
% 1.34/0.62    inference(avatar_component_clause,[],[f325])).
% 1.34/0.62  fof(f1009,plain,(
% 1.34/0.62    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (~spl6_6 | spl6_16 | ~spl6_41 | ~spl6_95)),
% 1.34/0.62    inference(forward_demodulation,[],[f1008,f644])).
% 1.34/0.62  fof(f644,plain,(
% 1.34/0.62    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl6_95),
% 1.34/0.62    inference(avatar_component_clause,[],[f642])).
% 1.34/0.62  fof(f1008,plain,(
% 1.34/0.62    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | (~spl6_6 | spl6_16 | ~spl6_41)),
% 1.34/0.62    inference(forward_demodulation,[],[f1007,f293])).
% 1.34/0.62  fof(f293,plain,(
% 1.34/0.62    ( ! [X1] : (k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))) ) | ~spl6_6),
% 1.34/0.62    inference(resolution,[],[f90,f124])).
% 1.34/0.62  fof(f124,plain,(
% 1.34/0.62    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl6_6),
% 1.34/0.62    inference(avatar_component_clause,[],[f122])).
% 1.34/0.62  fof(f90,plain,(
% 1.34/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 1.34/0.62    inference(definition_unfolding,[],[f82,f71])).
% 1.34/0.62  fof(f71,plain,(
% 1.34/0.62    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.34/0.62    inference(cnf_transformation,[],[f4])).
% 1.34/0.62  fof(f4,axiom,(
% 1.34/0.62    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.34/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.34/0.62  fof(f82,plain,(
% 1.34/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.34/0.62    inference(cnf_transformation,[],[f43])).
% 1.34/0.62  fof(f43,plain,(
% 1.34/0.62    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.34/0.62    inference(ennf_transformation,[],[f2])).
% 1.34/0.62  fof(f2,axiom,(
% 1.34/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.34/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.34/0.62  fof(f1007,plain,(
% 1.34/0.62    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (spl6_16 | ~spl6_41)),
% 1.34/0.62    inference(forward_demodulation,[],[f172,f330])).
% 1.34/0.62  fof(f330,plain,(
% 1.34/0.62    ( ! [X1] : (k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl6_41),
% 1.34/0.62    inference(avatar_component_clause,[],[f329])).
% 1.34/0.62  fof(f172,plain,(
% 1.34/0.62    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_16),
% 1.34/0.62    inference(avatar_component_clause,[],[f170])).
% 1.34/0.62  fof(f902,plain,(
% 1.34/0.62    spl6_14 | spl6_1 | ~spl6_101 | ~spl6_97 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_6 | spl6_7 | ~spl6_3 | spl6_4 | spl6_2 | ~spl6_6 | ~spl6_40 | ~spl6_41 | ~spl6_60 | ~spl6_85 | ~spl6_95 | ~spl6_131),
% 1.34/0.62    inference(avatar_split_clause,[],[f901,f839,f642,f567,f435,f329,f325,f122,f102,f112,f107,f127,f122,f142,f137,f132,f157,f152,f147,f654,f678,f97,f162])).
% 1.34/0.62  fof(f162,plain,(
% 1.34/0.62    spl6_14 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.34/0.62  fof(f97,plain,(
% 1.34/0.62    spl6_1 <=> v1_xboole_0(sK0)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.34/0.62  fof(f678,plain,(
% 1.34/0.62    spl6_101 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).
% 1.34/0.62  fof(f654,plain,(
% 1.34/0.62    spl6_97 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).
% 1.34/0.62  fof(f147,plain,(
% 1.34/0.62    spl6_11 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.34/0.62  fof(f152,plain,(
% 1.34/0.62    spl6_12 <=> v1_funct_2(sK5,sK3,sK1)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.34/0.62  fof(f157,plain,(
% 1.34/0.62    spl6_13 <=> v1_funct_1(sK5)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.34/0.62  fof(f132,plain,(
% 1.34/0.62    spl6_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.34/0.62  fof(f137,plain,(
% 1.34/0.62    spl6_9 <=> v1_funct_2(sK4,sK2,sK1)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.34/0.62  fof(f142,plain,(
% 1.34/0.62    spl6_10 <=> v1_funct_1(sK4)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.34/0.62  fof(f127,plain,(
% 1.34/0.62    spl6_7 <=> v1_xboole_0(sK3)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.34/0.62  fof(f107,plain,(
% 1.34/0.62    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.34/0.62  fof(f112,plain,(
% 1.34/0.62    spl6_4 <=> v1_xboole_0(sK2)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.34/0.62  fof(f102,plain,(
% 1.34/0.62    spl6_2 <=> v1_xboole_0(sK1)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.34/0.62  fof(f839,plain,(
% 1.34/0.62    spl6_131 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_131])])).
% 1.34/0.62  fof(f901,plain,(
% 1.34/0.62    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_40 | ~spl6_41 | ~spl6_60 | ~spl6_85 | ~spl6_95 | ~spl6_131)),
% 1.34/0.62    inference(trivial_inequality_removal,[],[f900])).
% 1.34/0.62  fof(f900,plain,(
% 1.34/0.62    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_40 | ~spl6_41 | ~spl6_60 | ~spl6_85 | ~spl6_95 | ~spl6_131)),
% 1.34/0.62    inference(forward_demodulation,[],[f899,f437])).
% 1.34/0.62  fof(f437,plain,(
% 1.34/0.62    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl6_60),
% 1.34/0.62    inference(avatar_component_clause,[],[f435])).
% 1.34/0.62  fof(f899,plain,(
% 1.34/0.62    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_40 | ~spl6_41 | ~spl6_85 | ~spl6_95 | ~spl6_131)),
% 1.34/0.62    inference(forward_demodulation,[],[f898,f569])).
% 1.34/0.62  fof(f898,plain,(
% 1.34/0.62    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_40 | ~spl6_41 | ~spl6_95 | ~spl6_131)),
% 1.34/0.62    inference(forward_demodulation,[],[f897,f326])).
% 1.34/0.62  fof(f897,plain,(
% 1.34/0.62    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_41 | ~spl6_95 | ~spl6_131)),
% 1.34/0.62    inference(forward_demodulation,[],[f896,f644])).
% 1.34/0.62  fof(f896,plain,(
% 1.34/0.62    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_6 | ~spl6_41 | ~spl6_131)),
% 1.34/0.62    inference(forward_demodulation,[],[f895,f293])).
% 1.34/0.62  fof(f895,plain,(
% 1.34/0.62    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_41 | ~spl6_131)),
% 1.34/0.62    inference(forward_demodulation,[],[f865,f330])).
% 1.34/0.62  fof(f865,plain,(
% 1.34/0.62    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~spl6_131),
% 1.34/0.62    inference(resolution,[],[f841,f93])).
% 1.34/0.62  fof(f93,plain,(
% 1.34/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 1.34/0.62    inference(equality_resolution,[],[f67])).
% 1.34/0.62  fof(f67,plain,(
% 1.34/0.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.34/0.62    inference(cnf_transformation,[],[f26])).
% 1.34/0.62  fof(f26,plain,(
% 1.34/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.34/0.62    inference(flattening,[],[f25])).
% 1.34/0.62  fof(f25,plain,(
% 1.34/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.34/0.62    inference(ennf_transformation,[],[f18])).
% 1.34/0.62  fof(f18,axiom,(
% 1.34/0.62    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 1.34/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 1.34/0.62  fof(f841,plain,(
% 1.34/0.62    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl6_131),
% 1.34/0.62    inference(avatar_component_clause,[],[f839])).
% 1.34/0.62  fof(f894,plain,(
% 1.34/0.62    spl6_15 | spl6_1 | ~spl6_101 | ~spl6_97 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_6 | spl6_7 | ~spl6_3 | spl6_4 | spl6_2 | ~spl6_6 | ~spl6_40 | ~spl6_41 | ~spl6_60 | ~spl6_85 | ~spl6_95 | ~spl6_131),
% 1.34/0.62    inference(avatar_split_clause,[],[f893,f839,f642,f567,f435,f329,f325,f122,f102,f112,f107,f127,f122,f142,f137,f132,f157,f152,f147,f654,f678,f97,f166])).
% 1.34/0.62  fof(f166,plain,(
% 1.34/0.62    spl6_15 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.34/0.62  fof(f893,plain,(
% 1.34/0.62    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_40 | ~spl6_41 | ~spl6_60 | ~spl6_85 | ~spl6_95 | ~spl6_131)),
% 1.34/0.62    inference(trivial_inequality_removal,[],[f892])).
% 1.34/0.62  fof(f892,plain,(
% 1.34/0.62    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_40 | ~spl6_41 | ~spl6_60 | ~spl6_85 | ~spl6_95 | ~spl6_131)),
% 1.34/0.62    inference(forward_demodulation,[],[f891,f437])).
% 1.34/0.62  fof(f891,plain,(
% 1.34/0.62    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_40 | ~spl6_41 | ~spl6_85 | ~spl6_95 | ~spl6_131)),
% 1.34/0.62    inference(forward_demodulation,[],[f890,f569])).
% 1.34/0.62  fof(f890,plain,(
% 1.34/0.62    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_40 | ~spl6_41 | ~spl6_95 | ~spl6_131)),
% 1.34/0.62    inference(forward_demodulation,[],[f889,f326])).
% 1.34/0.62  fof(f889,plain,(
% 1.34/0.62    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_41 | ~spl6_95 | ~spl6_131)),
% 1.34/0.62    inference(forward_demodulation,[],[f888,f644])).
% 1.34/0.62  fof(f888,plain,(
% 1.34/0.62    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_6 | ~spl6_41 | ~spl6_131)),
% 1.34/0.62    inference(forward_demodulation,[],[f887,f293])).
% 1.34/0.62  fof(f887,plain,(
% 1.34/0.62    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_41 | ~spl6_131)),
% 1.34/0.62    inference(forward_demodulation,[],[f864,f330])).
% 1.34/0.62  fof(f864,plain,(
% 1.34/0.62    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~spl6_131),
% 1.34/0.62    inference(resolution,[],[f841,f94])).
% 1.34/0.62  fof(f94,plain,(
% 1.34/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 1.34/0.62    inference(equality_resolution,[],[f66])).
% 1.34/0.62  fof(f66,plain,(
% 1.34/0.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.34/0.62    inference(cnf_transformation,[],[f26])).
% 1.34/0.62  fof(f842,plain,(
% 1.34/0.62    spl6_131 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_84),
% 1.34/0.62    inference(avatar_split_clause,[],[f837,f561,f132,f137,f142,f839])).
% 1.34/0.62  fof(f561,plain,(
% 1.34/0.62    spl6_84 <=> ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).
% 1.34/0.62  fof(f837,plain,(
% 1.34/0.62    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_8 | ~spl6_84)),
% 1.34/0.62    inference(resolution,[],[f562,f134])).
% 1.34/0.62  fof(f134,plain,(
% 1.34/0.62    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl6_8),
% 1.34/0.62    inference(avatar_component_clause,[],[f132])).
% 1.34/0.62  fof(f562,plain,(
% 1.34/0.62    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))) ) | ~spl6_84),
% 1.34/0.62    inference(avatar_component_clause,[],[f561])).
% 1.34/0.62  fof(f681,plain,(
% 1.34/0.62    spl6_101 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_80),
% 1.34/0.62    inference(avatar_split_clause,[],[f676,f541,f132,f137,f142,f678])).
% 1.34/0.62  fof(f541,plain,(
% 1.34/0.62    spl6_80 <=> ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).
% 1.34/0.62  fof(f676,plain,(
% 1.34/0.62    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_8 | ~spl6_80)),
% 1.34/0.62    inference(resolution,[],[f542,f134])).
% 1.34/0.62  fof(f542,plain,(
% 1.34/0.62    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)) ) | ~spl6_80),
% 1.34/0.62    inference(avatar_component_clause,[],[f541])).
% 1.34/0.62  fof(f657,plain,(
% 1.34/0.62    spl6_97 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_64),
% 1.34/0.62    inference(avatar_split_clause,[],[f652,f459,f132,f137,f142,f654])).
% 1.34/0.62  fof(f459,plain,(
% 1.34/0.62    spl6_64 <=> ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 1.34/0.62  fof(f652,plain,(
% 1.34/0.62    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_8 | ~spl6_64)),
% 1.34/0.62    inference(resolution,[],[f460,f134])).
% 1.34/0.62  fof(f460,plain,(
% 1.34/0.62    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))) ) | ~spl6_64),
% 1.34/0.62    inference(avatar_component_clause,[],[f459])).
% 1.34/0.62  fof(f645,plain,(
% 1.34/0.62    spl6_95 | ~spl6_22 | ~spl6_48 | ~spl6_69),
% 1.34/0.62    inference(avatar_split_clause,[],[f640,f488,f368,f204,f642])).
% 1.34/0.62  fof(f204,plain,(
% 1.34/0.62    spl6_22 <=> v1_relat_1(sK5)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.34/0.62  fof(f368,plain,(
% 1.34/0.62    spl6_48 <=> sK3 = k10_relat_1(sK5,k2_relat_1(sK5))),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 1.34/0.62  fof(f488,plain,(
% 1.34/0.62    spl6_69 <=> k1_xboole_0 = k7_relat_1(sK5,sK2)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).
% 1.34/0.62  fof(f640,plain,(
% 1.34/0.62    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | (~spl6_22 | ~spl6_48 | ~spl6_69)),
% 1.34/0.62    inference(forward_demodulation,[],[f632,f65])).
% 1.34/0.62  fof(f65,plain,(
% 1.34/0.62    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 1.34/0.62    inference(cnf_transformation,[],[f7])).
% 1.34/0.62  fof(f7,axiom,(
% 1.34/0.62    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.34/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 1.34/0.62  fof(f632,plain,(
% 1.34/0.62    k1_setfam_1(k2_tarski(sK2,sK3)) = k10_relat_1(k1_xboole_0,k2_relat_1(sK5)) | (~spl6_22 | ~spl6_48 | ~spl6_69)),
% 1.34/0.62    inference(superposition,[],[f624,f490])).
% 1.34/0.62  fof(f490,plain,(
% 1.34/0.62    k1_xboole_0 = k7_relat_1(sK5,sK2) | ~spl6_69),
% 1.34/0.62    inference(avatar_component_clause,[],[f488])).
% 1.34/0.62  fof(f624,plain,(
% 1.34/0.62    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,sK3)) = k10_relat_1(k7_relat_1(sK5,X0),k2_relat_1(sK5))) ) | (~spl6_22 | ~spl6_48)),
% 1.34/0.62    inference(superposition,[],[f303,f370])).
% 1.34/0.62  fof(f370,plain,(
% 1.34/0.62    sK3 = k10_relat_1(sK5,k2_relat_1(sK5)) | ~spl6_48),
% 1.34/0.62    inference(avatar_component_clause,[],[f368])).
% 1.34/0.62  fof(f303,plain,(
% 1.34/0.62    ( ! [X2,X3] : (k10_relat_1(k7_relat_1(sK5,X2),X3) = k1_setfam_1(k2_tarski(X2,k10_relat_1(sK5,X3)))) ) | ~spl6_22),
% 1.34/0.62    inference(resolution,[],[f89,f206])).
% 1.34/0.62  fof(f206,plain,(
% 1.34/0.62    v1_relat_1(sK5) | ~spl6_22),
% 1.34/0.62    inference(avatar_component_clause,[],[f204])).
% 1.34/0.62  fof(f89,plain,(
% 1.34/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1)))) )),
% 1.34/0.62    inference(definition_unfolding,[],[f80,f71])).
% 1.34/0.62  fof(f80,plain,(
% 1.34/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 1.34/0.62    inference(cnf_transformation,[],[f40])).
% 1.34/0.62  fof(f40,plain,(
% 1.34/0.62    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.34/0.62    inference(ennf_transformation,[],[f12])).
% 1.34/0.62  fof(f12,axiom,(
% 1.34/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.34/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.34/0.62  fof(f570,plain,(
% 1.34/0.62    spl6_85 | ~spl6_22 | ~spl6_34),
% 1.34/0.62    inference(avatar_split_clause,[],[f564,f279,f204,f567])).
% 1.34/0.62  fof(f279,plain,(
% 1.34/0.62    spl6_34 <=> sK5 = k7_relat_1(sK5,sK3)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 1.34/0.62  fof(f564,plain,(
% 1.34/0.62    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | (~spl6_22 | ~spl6_34)),
% 1.34/0.62    inference(superposition,[],[f478,f281])).
% 1.34/0.62  fof(f281,plain,(
% 1.34/0.62    sK5 = k7_relat_1(sK5,sK3) | ~spl6_34),
% 1.34/0.62    inference(avatar_component_clause,[],[f279])).
% 1.34/0.62  fof(f478,plain,(
% 1.34/0.62    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK5,X0),k1_xboole_0)) ) | ~spl6_22),
% 1.34/0.62    inference(resolution,[],[f285,f64])).
% 1.34/0.62  fof(f64,plain,(
% 1.34/0.62    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.34/0.62    inference(cnf_transformation,[],[f1])).
% 1.34/0.62  fof(f1,axiom,(
% 1.34/0.62    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.34/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.34/0.62  fof(f285,plain,(
% 1.34/0.62    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK5,X2),X3)) ) | ~spl6_22),
% 1.34/0.62    inference(resolution,[],[f81,f206])).
% 1.34/0.62  fof(f81,plain,(
% 1.34/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 1.34/0.62    inference(cnf_transformation,[],[f42])).
% 1.34/0.62  fof(f42,plain,(
% 1.34/0.62    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 1.34/0.62    inference(flattening,[],[f41])).
% 1.34/0.62  fof(f41,plain,(
% 1.34/0.62    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.34/0.62    inference(ennf_transformation,[],[f8])).
% 1.34/0.62  fof(f8,axiom,(
% 1.34/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 1.34/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 1.34/0.62  fof(f563,plain,(
% 1.34/0.62    ~spl6_6 | ~spl6_12 | spl6_7 | ~spl6_13 | spl6_2 | spl6_84 | ~spl6_11 | ~spl6_53),
% 1.34/0.62    inference(avatar_split_clause,[],[f555,f397,f147,f561,f102,f157,f127,f152,f122])).
% 1.34/0.62  fof(f397,plain,(
% 1.34/0.62    spl6_53 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 1.34/0.62  fof(f555,plain,(
% 1.34/0.62    ( ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl6_11 | ~spl6_53)),
% 1.34/0.62    inference(resolution,[],[f398,f149])).
% 1.34/0.62  fof(f149,plain,(
% 1.34/0.62    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl6_11),
% 1.34/0.62    inference(avatar_component_clause,[],[f147])).
% 1.34/0.62  fof(f398,plain,(
% 1.34/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl6_53),
% 1.34/0.62    inference(avatar_component_clause,[],[f397])).
% 1.34/0.62  fof(f543,plain,(
% 1.34/0.62    ~spl6_6 | ~spl6_12 | spl6_7 | ~spl6_13 | spl6_2 | spl6_80 | ~spl6_11 | ~spl6_49),
% 1.34/0.62    inference(avatar_split_clause,[],[f535,f377,f147,f541,f102,f157,f127,f152,f122])).
% 1.34/0.62  fof(f377,plain,(
% 1.34/0.62    spl6_49 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 1.34/0.62  fof(f535,plain,(
% 1.34/0.62    ( ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl6_11 | ~spl6_49)),
% 1.34/0.62    inference(resolution,[],[f378,f149])).
% 1.34/0.62  fof(f378,plain,(
% 1.34/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl6_49),
% 1.34/0.62    inference(avatar_component_clause,[],[f377])).
% 1.34/0.62  fof(f491,plain,(
% 1.34/0.62    spl6_69 | ~spl6_22 | ~spl6_32 | ~spl6_34),
% 1.34/0.62    inference(avatar_split_clause,[],[f486,f279,f266,f204,f488])).
% 1.34/0.62  fof(f266,plain,(
% 1.34/0.62    spl6_32 <=> r1_xboole_0(sK3,sK2)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 1.34/0.62  fof(f486,plain,(
% 1.34/0.62    k1_xboole_0 = k7_relat_1(sK5,sK2) | (~spl6_22 | ~spl6_32 | ~spl6_34)),
% 1.34/0.62    inference(forward_demodulation,[],[f480,f281])).
% 1.34/0.62  fof(f480,plain,(
% 1.34/0.62    k1_xboole_0 = k7_relat_1(k7_relat_1(sK5,sK3),sK2) | (~spl6_22 | ~spl6_32)),
% 1.34/0.62    inference(resolution,[],[f285,f268])).
% 1.34/0.62  fof(f268,plain,(
% 1.34/0.62    r1_xboole_0(sK3,sK2) | ~spl6_32),
% 1.34/0.62    inference(avatar_component_clause,[],[f266])).
% 1.34/0.62  fof(f461,plain,(
% 1.34/0.62    ~spl6_6 | ~spl6_12 | spl6_7 | ~spl6_13 | spl6_2 | spl6_64 | ~spl6_11 | ~spl6_44),
% 1.34/0.62    inference(avatar_split_clause,[],[f453,f350,f147,f459,f102,f157,f127,f152,f122])).
% 1.34/0.62  fof(f350,plain,(
% 1.34/0.62    spl6_44 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 1.34/0.62  fof(f453,plain,(
% 1.34/0.62    ( ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl6_11 | ~spl6_44)),
% 1.34/0.62    inference(resolution,[],[f351,f149])).
% 1.34/0.62  fof(f351,plain,(
% 1.34/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl6_44),
% 1.34/0.62    inference(avatar_component_clause,[],[f350])).
% 1.34/0.62  fof(f438,plain,(
% 1.34/0.62    spl6_60 | ~spl6_21 | ~spl6_33),
% 1.34/0.62    inference(avatar_split_clause,[],[f432,f274,f199,f435])).
% 1.34/0.62  fof(f199,plain,(
% 1.34/0.62    spl6_21 <=> v1_relat_1(sK4)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.34/0.62  fof(f274,plain,(
% 1.34/0.62    spl6_33 <=> sK4 = k7_relat_1(sK4,sK2)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 1.34/0.62  fof(f432,plain,(
% 1.34/0.62    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | (~spl6_21 | ~spl6_33)),
% 1.34/0.62    inference(superposition,[],[f412,f276])).
% 1.34/0.62  fof(f276,plain,(
% 1.34/0.62    sK4 = k7_relat_1(sK4,sK2) | ~spl6_33),
% 1.34/0.62    inference(avatar_component_clause,[],[f274])).
% 1.34/0.62  fof(f412,plain,(
% 1.34/0.62    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,X0),k1_xboole_0)) ) | ~spl6_21),
% 1.34/0.62    inference(resolution,[],[f284,f64])).
% 1.34/0.62  fof(f284,plain,(
% 1.34/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,X0),X1)) ) | ~spl6_21),
% 1.34/0.62    inference(resolution,[],[f81,f201])).
% 1.34/0.62  fof(f201,plain,(
% 1.34/0.62    v1_relat_1(sK4) | ~spl6_21),
% 1.34/0.62    inference(avatar_component_clause,[],[f199])).
% 1.34/0.62  fof(f399,plain,(
% 1.34/0.62    spl6_1 | spl6_4 | spl6_53 | ~spl6_3),
% 1.34/0.62    inference(avatar_split_clause,[],[f392,f107,f397,f112,f97])).
% 1.34/0.62  fof(f392,plain,(
% 1.34/0.62    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0)))) ) | ~spl6_3),
% 1.34/0.62    inference(resolution,[],[f88,f109])).
% 1.34/0.62  fof(f109,plain,(
% 1.34/0.62    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl6_3),
% 1.34/0.62    inference(avatar_component_clause,[],[f107])).
% 1.34/0.62  fof(f88,plain,(
% 1.34/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 1.34/0.62    inference(cnf_transformation,[],[f49])).
% 1.34/0.62  fof(f49,plain,(
% 1.34/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.34/0.62    inference(flattening,[],[f48])).
% 1.34/0.62  fof(f48,plain,(
% 1.34/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.34/0.62    inference(ennf_transformation,[],[f19])).
% 1.34/0.62  fof(f19,axiom,(
% 1.34/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.34/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 1.34/0.62  fof(f379,plain,(
% 1.34/0.62    spl6_1 | spl6_4 | spl6_49 | ~spl6_3),
% 1.34/0.62    inference(avatar_split_clause,[],[f372,f107,f377,f112,f97])).
% 1.34/0.62  fof(f372,plain,(
% 1.34/0.62    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0)) ) | ~spl6_3),
% 1.34/0.62    inference(resolution,[],[f87,f109])).
% 1.34/0.62  fof(f87,plain,(
% 1.34/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 1.34/0.62    inference(cnf_transformation,[],[f49])).
% 1.34/0.62  fof(f371,plain,(
% 1.34/0.62    spl6_48 | ~spl6_24 | ~spl6_42),
% 1.34/0.62    inference(avatar_split_clause,[],[f365,f334,f216,f368])).
% 1.34/0.62  fof(f216,plain,(
% 1.34/0.62    spl6_24 <=> k10_relat_1(sK5,k2_relat_1(sK5)) = k1_relat_1(sK5)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.34/0.62  fof(f334,plain,(
% 1.34/0.62    spl6_42 <=> sK3 = k1_relat_1(sK5)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 1.34/0.62  fof(f365,plain,(
% 1.34/0.62    sK3 = k10_relat_1(sK5,k2_relat_1(sK5)) | (~spl6_24 | ~spl6_42)),
% 1.34/0.62    inference(backward_demodulation,[],[f218,f336])).
% 1.34/0.62  fof(f336,plain,(
% 1.34/0.62    sK3 = k1_relat_1(sK5) | ~spl6_42),
% 1.34/0.62    inference(avatar_component_clause,[],[f334])).
% 1.34/0.62  fof(f218,plain,(
% 1.34/0.62    k10_relat_1(sK5,k2_relat_1(sK5)) = k1_relat_1(sK5) | ~spl6_24),
% 1.34/0.62    inference(avatar_component_clause,[],[f216])).
% 1.34/0.62  fof(f352,plain,(
% 1.34/0.62    spl6_1 | spl6_4 | spl6_44 | ~spl6_3),
% 1.34/0.62    inference(avatar_split_clause,[],[f345,f107,f350,f112,f97])).
% 1.34/0.62  fof(f345,plain,(
% 1.34/0.62    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3))) ) | ~spl6_3),
% 1.34/0.62    inference(resolution,[],[f86,f109])).
% 1.34/0.62  fof(f86,plain,(
% 1.34/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 1.34/0.62    inference(cnf_transformation,[],[f49])).
% 1.34/0.62  fof(f337,plain,(
% 1.34/0.62    ~spl6_22 | spl6_42 | ~spl6_26 | ~spl6_38),
% 1.34/0.62    inference(avatar_split_clause,[],[f332,f312,f228,f334,f204])).
% 1.34/0.62  fof(f228,plain,(
% 1.34/0.62    spl6_26 <=> v4_relat_1(sK5,sK3)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.34/0.62  fof(f312,plain,(
% 1.34/0.62    spl6_38 <=> v1_partfun1(sK5,sK3)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 1.34/0.62  fof(f332,plain,(
% 1.34/0.62    ~v4_relat_1(sK5,sK3) | sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5) | ~spl6_38),
% 1.34/0.62    inference(resolution,[],[f314,f79])).
% 1.34/0.62  fof(f79,plain,(
% 1.34/0.62    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 1.34/0.62    inference(cnf_transformation,[],[f39])).
% 1.34/0.62  fof(f39,plain,(
% 1.34/0.62    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.34/0.62    inference(flattening,[],[f38])).
% 1.34/0.62  fof(f38,plain,(
% 1.34/0.62    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.34/0.62    inference(ennf_transformation,[],[f16])).
% 1.34/0.62  fof(f16,axiom,(
% 1.34/0.62    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.34/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 1.34/0.62  fof(f314,plain,(
% 1.34/0.62    v1_partfun1(sK5,sK3) | ~spl6_38),
% 1.34/0.62    inference(avatar_component_clause,[],[f312])).
% 1.34/0.62  fof(f331,plain,(
% 1.34/0.62    spl6_41 | ~spl6_13 | ~spl6_11),
% 1.34/0.62    inference(avatar_split_clause,[],[f323,f147,f157,f329])).
% 1.34/0.62  fof(f323,plain,(
% 1.34/0.62    ( ! [X1] : (~v1_funct_1(sK5) | k7_relat_1(sK5,X1) = k2_partfun1(sK3,sK1,sK5,X1)) ) | ~spl6_11),
% 1.34/0.62    inference(resolution,[],[f85,f149])).
% 1.34/0.62  fof(f85,plain,(
% 1.34/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.34/0.62    inference(cnf_transformation,[],[f47])).
% 1.34/0.62  fof(f47,plain,(
% 1.34/0.62    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.34/0.62    inference(flattening,[],[f46])).
% 1.34/0.62  fof(f46,plain,(
% 1.34/0.62    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.34/0.62    inference(ennf_transformation,[],[f17])).
% 1.34/0.62  fof(f17,axiom,(
% 1.34/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.34/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.34/0.62  fof(f327,plain,(
% 1.34/0.62    spl6_40 | ~spl6_10 | ~spl6_8),
% 1.34/0.62    inference(avatar_split_clause,[],[f322,f132,f142,f325])).
% 1.34/0.62  fof(f322,plain,(
% 1.34/0.62    ( ! [X0] : (~v1_funct_1(sK4) | k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) ) | ~spl6_8),
% 1.34/0.62    inference(resolution,[],[f85,f134])).
% 1.34/0.62  fof(f315,plain,(
% 1.34/0.62    spl6_38 | ~spl6_12 | ~spl6_13 | spl6_2 | ~spl6_11),
% 1.34/0.62    inference(avatar_split_clause,[],[f305,f147,f102,f157,f152,f312])).
% 1.34/0.62  fof(f305,plain,(
% 1.34/0.62    v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3) | ~spl6_11),
% 1.34/0.62    inference(resolution,[],[f72,f149])).
% 1.34/0.62  fof(f72,plain,(
% 1.34/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 1.34/0.62    inference(cnf_transformation,[],[f30])).
% 1.34/0.62  fof(f30,plain,(
% 1.34/0.62    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.34/0.62    inference(flattening,[],[f29])).
% 1.34/0.62  fof(f29,plain,(
% 1.34/0.62    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.34/0.62    inference(ennf_transformation,[],[f15])).
% 1.34/0.62  fof(f15,axiom,(
% 1.34/0.62    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.34/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.34/0.62  fof(f282,plain,(
% 1.34/0.62    spl6_34 | ~spl6_22 | ~spl6_26),
% 1.34/0.62    inference(avatar_split_clause,[],[f272,f228,f204,f279])).
% 1.34/0.62  fof(f272,plain,(
% 1.34/0.62    ~v1_relat_1(sK5) | sK5 = k7_relat_1(sK5,sK3) | ~spl6_26),
% 1.34/0.62    inference(resolution,[],[f77,f230])).
% 1.34/0.62  fof(f230,plain,(
% 1.34/0.62    v4_relat_1(sK5,sK3) | ~spl6_26),
% 1.34/0.62    inference(avatar_component_clause,[],[f228])).
% 1.34/0.62  fof(f77,plain,(
% 1.34/0.62    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 1.34/0.62    inference(cnf_transformation,[],[f37])).
% 1.34/0.62  fof(f37,plain,(
% 1.34/0.62    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.34/0.62    inference(flattening,[],[f36])).
% 1.34/0.62  fof(f36,plain,(
% 1.34/0.62    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.34/0.62    inference(ennf_transformation,[],[f9])).
% 1.34/0.62  fof(f9,axiom,(
% 1.34/0.62    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.34/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.34/0.62  fof(f277,plain,(
% 1.34/0.62    spl6_33 | ~spl6_21 | ~spl6_25),
% 1.34/0.62    inference(avatar_split_clause,[],[f271,f223,f199,f274])).
% 1.34/0.62  fof(f223,plain,(
% 1.34/0.62    spl6_25 <=> v4_relat_1(sK4,sK2)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.34/0.62  fof(f271,plain,(
% 1.34/0.62    ~v1_relat_1(sK4) | sK4 = k7_relat_1(sK4,sK2) | ~spl6_25),
% 1.34/0.62    inference(resolution,[],[f77,f225])).
% 1.34/0.62  fof(f225,plain,(
% 1.34/0.62    v4_relat_1(sK4,sK2) | ~spl6_25),
% 1.34/0.62    inference(avatar_component_clause,[],[f223])).
% 1.34/0.62  fof(f269,plain,(
% 1.34/0.62    spl6_7 | spl6_32 | spl6_4 | ~spl6_27),
% 1.34/0.62    inference(avatar_split_clause,[],[f257,f236,f112,f266,f127])).
% 1.34/0.62  fof(f236,plain,(
% 1.34/0.62    spl6_27 <=> r1_subset_1(sK3,sK2)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.34/0.62  fof(f257,plain,(
% 1.34/0.62    v1_xboole_0(sK2) | r1_xboole_0(sK3,sK2) | v1_xboole_0(sK3) | ~spl6_27),
% 1.34/0.62    inference(resolution,[],[f76,f238])).
% 1.34/0.62  fof(f238,plain,(
% 1.34/0.62    r1_subset_1(sK3,sK2) | ~spl6_27),
% 1.34/0.62    inference(avatar_component_clause,[],[f236])).
% 1.34/0.62  fof(f76,plain,(
% 1.34/0.62    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 1.34/0.62    inference(cnf_transformation,[],[f35])).
% 1.34/0.62  fof(f35,plain,(
% 1.34/0.62    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.34/0.62    inference(flattening,[],[f34])).
% 1.34/0.62  fof(f34,plain,(
% 1.34/0.62    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.34/0.62    inference(ennf_transformation,[],[f10])).
% 1.34/0.62  fof(f10,axiom,(
% 1.34/0.62    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 1.34/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 1.34/0.62  fof(f239,plain,(
% 1.34/0.62    spl6_27 | spl6_4 | spl6_7 | ~spl6_5),
% 1.34/0.62    inference(avatar_split_clause,[],[f234,f117,f127,f112,f236])).
% 1.34/0.62  fof(f117,plain,(
% 1.34/0.62    spl6_5 <=> r1_subset_1(sK2,sK3)),
% 1.34/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.34/0.62  fof(f234,plain,(
% 1.34/0.62    v1_xboole_0(sK3) | v1_xboole_0(sK2) | r1_subset_1(sK3,sK2) | ~spl6_5),
% 1.34/0.62    inference(resolution,[],[f74,f119])).
% 1.34/0.62  fof(f119,plain,(
% 1.34/0.62    r1_subset_1(sK2,sK3) | ~spl6_5),
% 1.34/0.62    inference(avatar_component_clause,[],[f117])).
% 1.34/0.62  fof(f74,plain,(
% 1.34/0.62    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | r1_subset_1(X1,X0)) )),
% 1.34/0.62    inference(cnf_transformation,[],[f33])).
% 1.34/0.62  fof(f33,plain,(
% 1.34/0.62    ! [X0,X1] : (r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.34/0.62    inference(flattening,[],[f32])).
% 1.34/0.62  fof(f32,plain,(
% 1.34/0.62    ! [X0,X1] : ((r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.34/0.62    inference(ennf_transformation,[],[f11])).
% 1.34/0.62  fof(f11,axiom,(
% 1.34/0.62    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) => r1_subset_1(X1,X0)))),
% 1.34/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_subset_1)).
% 1.34/0.62  fof(f231,plain,(
% 1.34/0.62    spl6_26 | ~spl6_11),
% 1.34/0.62    inference(avatar_split_clause,[],[f221,f147,f228])).
% 1.34/0.62  fof(f221,plain,(
% 1.34/0.62    v4_relat_1(sK5,sK3) | ~spl6_11),
% 1.34/0.62    inference(resolution,[],[f84,f149])).
% 1.34/0.62  fof(f84,plain,(
% 1.34/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.34/0.62    inference(cnf_transformation,[],[f45])).
% 1.34/0.62  fof(f45,plain,(
% 1.34/0.62    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.62    inference(ennf_transformation,[],[f22])).
% 1.34/0.62  fof(f22,plain,(
% 1.34/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.34/0.62    inference(pure_predicate_removal,[],[f14])).
% 1.34/0.62  fof(f14,axiom,(
% 1.34/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.34/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.34/0.62  fof(f226,plain,(
% 1.34/0.62    spl6_25 | ~spl6_8),
% 1.34/0.62    inference(avatar_split_clause,[],[f220,f132,f223])).
% 1.34/0.62  fof(f220,plain,(
% 1.34/0.62    v4_relat_1(sK4,sK2) | ~spl6_8),
% 1.34/0.62    inference(resolution,[],[f84,f134])).
% 1.34/0.62  fof(f219,plain,(
% 1.34/0.62    spl6_24 | ~spl6_22),
% 1.34/0.62    inference(avatar_split_clause,[],[f214,f204,f216])).
% 1.34/0.62  fof(f214,plain,(
% 1.34/0.62    k10_relat_1(sK5,k2_relat_1(sK5)) = k1_relat_1(sK5) | ~spl6_22),
% 1.34/0.62    inference(resolution,[],[f206,f69])).
% 1.34/0.62  fof(f69,plain,(
% 1.34/0.62    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.34/0.62    inference(cnf_transformation,[],[f27])).
% 1.34/0.62  fof(f27,plain,(
% 1.34/0.62    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.34/0.62    inference(ennf_transformation,[],[f6])).
% 1.34/0.62  fof(f6,axiom,(
% 1.34/0.62    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.34/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.34/0.62  fof(f207,plain,(
% 1.34/0.62    spl6_22 | ~spl6_11),
% 1.34/0.62    inference(avatar_split_clause,[],[f197,f147,f204])).
% 1.34/0.62  fof(f197,plain,(
% 1.34/0.62    v1_relat_1(sK5) | ~spl6_11),
% 1.34/0.62    inference(resolution,[],[f83,f149])).
% 1.34/0.62  fof(f83,plain,(
% 1.34/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.34/0.62    inference(cnf_transformation,[],[f44])).
% 1.34/0.62  fof(f44,plain,(
% 1.34/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.62    inference(ennf_transformation,[],[f13])).
% 1.34/0.62  fof(f13,axiom,(
% 1.34/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.34/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.34/0.62  fof(f202,plain,(
% 1.34/0.62    spl6_21 | ~spl6_8),
% 1.34/0.62    inference(avatar_split_clause,[],[f196,f132,f199])).
% 1.34/0.62  fof(f196,plain,(
% 1.34/0.62    v1_relat_1(sK4) | ~spl6_8),
% 1.34/0.62    inference(resolution,[],[f83,f134])).
% 1.34/0.62  fof(f173,plain,(
% 1.34/0.62    ~spl6_14 | ~spl6_15 | ~spl6_16),
% 1.34/0.62    inference(avatar_split_clause,[],[f50,f170,f166,f162])).
% 1.34/0.62  fof(f50,plain,(
% 1.34/0.62    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.34/0.62    inference(cnf_transformation,[],[f24])).
% 1.34/0.62  fof(f24,plain,(
% 1.34/0.62    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.34/0.62    inference(flattening,[],[f23])).
% 1.34/0.62  fof(f23,plain,(
% 1.34/0.62    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.34/0.62    inference(ennf_transformation,[],[f21])).
% 1.34/0.62  fof(f21,negated_conjecture,(
% 1.34/0.62    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.34/0.62    inference(negated_conjecture,[],[f20])).
% 1.34/0.62  fof(f20,conjecture,(
% 1.34/0.62    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.34/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 1.34/0.62  fof(f160,plain,(
% 1.34/0.62    spl6_13),
% 1.34/0.62    inference(avatar_split_clause,[],[f51,f157])).
% 1.34/0.62  fof(f51,plain,(
% 1.34/0.62    v1_funct_1(sK5)),
% 1.34/0.62    inference(cnf_transformation,[],[f24])).
% 1.34/0.62  fof(f155,plain,(
% 1.34/0.62    spl6_12),
% 1.34/0.62    inference(avatar_split_clause,[],[f52,f152])).
% 1.34/0.62  fof(f52,plain,(
% 1.34/0.62    v1_funct_2(sK5,sK3,sK1)),
% 1.34/0.62    inference(cnf_transformation,[],[f24])).
% 1.34/0.62  fof(f150,plain,(
% 1.34/0.62    spl6_11),
% 1.34/0.62    inference(avatar_split_clause,[],[f53,f147])).
% 1.34/0.62  fof(f53,plain,(
% 1.34/0.62    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.34/0.62    inference(cnf_transformation,[],[f24])).
% 1.34/0.62  fof(f145,plain,(
% 1.34/0.62    spl6_10),
% 1.34/0.62    inference(avatar_split_clause,[],[f54,f142])).
% 1.34/0.62  fof(f54,plain,(
% 1.34/0.62    v1_funct_1(sK4)),
% 1.34/0.62    inference(cnf_transformation,[],[f24])).
% 1.34/0.62  fof(f140,plain,(
% 1.34/0.62    spl6_9),
% 1.34/0.62    inference(avatar_split_clause,[],[f55,f137])).
% 1.34/0.62  fof(f55,plain,(
% 1.34/0.62    v1_funct_2(sK4,sK2,sK1)),
% 1.34/0.62    inference(cnf_transformation,[],[f24])).
% 1.34/0.62  fof(f135,plain,(
% 1.34/0.62    spl6_8),
% 1.34/0.62    inference(avatar_split_clause,[],[f56,f132])).
% 1.34/0.62  fof(f56,plain,(
% 1.34/0.62    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.34/0.62    inference(cnf_transformation,[],[f24])).
% 1.34/0.62  fof(f130,plain,(
% 1.34/0.62    ~spl6_7),
% 1.34/0.62    inference(avatar_split_clause,[],[f57,f127])).
% 1.34/0.62  fof(f57,plain,(
% 1.34/0.62    ~v1_xboole_0(sK3)),
% 1.34/0.62    inference(cnf_transformation,[],[f24])).
% 1.34/0.62  fof(f125,plain,(
% 1.34/0.62    spl6_6),
% 1.34/0.62    inference(avatar_split_clause,[],[f58,f122])).
% 1.34/0.62  fof(f58,plain,(
% 1.34/0.62    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.34/0.62    inference(cnf_transformation,[],[f24])).
% 1.34/0.62  fof(f120,plain,(
% 1.34/0.62    spl6_5),
% 1.34/0.62    inference(avatar_split_clause,[],[f59,f117])).
% 1.34/0.62  fof(f59,plain,(
% 1.34/0.62    r1_subset_1(sK2,sK3)),
% 1.34/0.62    inference(cnf_transformation,[],[f24])).
% 1.34/0.62  fof(f115,plain,(
% 1.34/0.62    ~spl6_4),
% 1.34/0.62    inference(avatar_split_clause,[],[f60,f112])).
% 1.34/0.62  fof(f60,plain,(
% 1.34/0.62    ~v1_xboole_0(sK2)),
% 1.34/0.62    inference(cnf_transformation,[],[f24])).
% 1.34/0.62  fof(f110,plain,(
% 1.34/0.62    spl6_3),
% 1.34/0.62    inference(avatar_split_clause,[],[f61,f107])).
% 1.34/0.62  fof(f61,plain,(
% 1.34/0.62    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.34/0.62    inference(cnf_transformation,[],[f24])).
% 1.34/0.62  fof(f105,plain,(
% 1.34/0.62    ~spl6_2),
% 1.34/0.62    inference(avatar_split_clause,[],[f62,f102])).
% 1.34/0.62  fof(f62,plain,(
% 1.34/0.62    ~v1_xboole_0(sK1)),
% 1.34/0.62    inference(cnf_transformation,[],[f24])).
% 1.34/0.62  fof(f100,plain,(
% 1.34/0.62    ~spl6_1),
% 1.34/0.62    inference(avatar_split_clause,[],[f63,f97])).
% 1.34/0.62  fof(f63,plain,(
% 1.34/0.62    ~v1_xboole_0(sK0)),
% 1.34/0.62    inference(cnf_transformation,[],[f24])).
% 1.34/0.62  % SZS output end Proof for theBenchmark
% 1.34/0.62  % (31547)------------------------------
% 1.34/0.62  % (31547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.62  % (31547)Termination reason: Refutation
% 1.34/0.62  
% 1.34/0.62  % (31547)Memory used [KB]: 11641
% 1.34/0.62  % (31547)Time elapsed: 0.187 s
% 1.34/0.62  % (31547)------------------------------
% 1.34/0.62  % (31547)------------------------------
% 1.34/0.62  % (31530)Success in time 0.257 s
%------------------------------------------------------------------------------
