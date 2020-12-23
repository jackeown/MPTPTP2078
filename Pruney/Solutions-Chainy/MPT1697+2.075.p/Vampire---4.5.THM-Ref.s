%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:40 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 495 expanded)
%              Number of leaves         :   50 ( 233 expanded)
%              Depth                    :   14
%              Number of atoms          : 1197 (2735 expanded)
%              Number of equality atoms :  109 ( 343 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f934,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f153,f158,f171,f176,f204,f213,f215,f240,f274,f282,f320,f325,f349,f353,f373,f395,f416,f526,f573,f593,f633,f657,f681,f835,f843,f933])).

fof(f933,plain,
    ( ~ spl8_36
    | ~ spl8_6
    | spl8_16
    | ~ spl8_32
    | ~ spl8_37
    | ~ spl8_41
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f932,f351,f347,f322,f279,f168,f120,f317])).

fof(f317,plain,
    ( spl8_36
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f120,plain,
    ( spl8_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f168,plain,
    ( spl8_16
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f279,plain,
    ( spl8_32
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f322,plain,
    ( spl8_37
  <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f347,plain,
    ( spl8_41
  <=> ! [X0] : k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f351,plain,
    ( spl8_42
  <=> ! [X1] : k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f932,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ spl8_6
    | spl8_16
    | ~ spl8_32
    | ~ spl8_37
    | ~ spl8_41
    | ~ spl8_42 ),
    inference(forward_demodulation,[],[f931,f324])).

fof(f324,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f322])).

fof(f931,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ spl8_6
    | spl8_16
    | ~ spl8_32
    | ~ spl8_41
    | ~ spl8_42 ),
    inference(forward_demodulation,[],[f930,f348])).

fof(f348,plain,
    ( ! [X0] : k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f347])).

fof(f930,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl8_6
    | spl8_16
    | ~ spl8_32
    | ~ spl8_42 ),
    inference(forward_demodulation,[],[f929,f281])).

fof(f281,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f279])).

fof(f929,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl8_6
    | spl8_16
    | ~ spl8_42 ),
    inference(forward_demodulation,[],[f928,f308])).

fof(f308,plain,
    ( ! [X1] : k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))
    | ~ spl8_6 ),
    inference(resolution,[],[f88,f122])).

fof(f122,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f120])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f80,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f928,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl8_16
    | ~ spl8_42 ),
    inference(forward_demodulation,[],[f170,f352])).

fof(f352,plain,
    ( ! [X1] : k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1)
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f351])).

fof(f170,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl8_16 ),
    inference(avatar_component_clause,[],[f168])).

fof(f843,plain,
    ( spl8_14
    | spl8_1
    | ~ spl8_84
    | ~ spl8_80
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
    | ~ spl8_32
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_41
    | ~ spl8_42
    | ~ spl8_88 ),
    inference(avatar_split_clause,[],[f842,f678,f351,f347,f322,f317,f279,f120,f100,f110,f105,f125,f120,f140,f135,f130,f155,f150,f145,f630,f654,f95,f160])).

fof(f160,plain,
    ( spl8_14
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f95,plain,
    ( spl8_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f654,plain,
    ( spl8_84
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).

fof(f630,plain,
    ( spl8_80
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f145,plain,
    ( spl8_11
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f150,plain,
    ( spl8_12
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f155,plain,
    ( spl8_13
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f130,plain,
    ( spl8_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f135,plain,
    ( spl8_9
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f140,plain,
    ( spl8_10
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f125,plain,
    ( spl8_7
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f105,plain,
    ( spl8_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f110,plain,
    ( spl8_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f100,plain,
    ( spl8_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f678,plain,
    ( spl8_88
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f842,plain,
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
    | ~ spl8_32
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_41
    | ~ spl8_42
    | ~ spl8_88 ),
    inference(trivial_inequality_removal,[],[f841])).

fof(f841,plain,
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
    | ~ spl8_32
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_41
    | ~ spl8_42
    | ~ spl8_88 ),
    inference(forward_demodulation,[],[f840,f319])).

fof(f319,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f317])).

fof(f840,plain,
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
    | ~ spl8_32
    | ~ spl8_37
    | ~ spl8_41
    | ~ spl8_42
    | ~ spl8_88 ),
    inference(forward_demodulation,[],[f839,f324])).

fof(f839,plain,
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
    | ~ spl8_32
    | ~ spl8_41
    | ~ spl8_42
    | ~ spl8_88 ),
    inference(forward_demodulation,[],[f838,f348])).

fof(f838,plain,
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
    | ~ spl8_32
    | ~ spl8_42
    | ~ spl8_88 ),
    inference(forward_demodulation,[],[f837,f281])).

fof(f837,plain,
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
    | ~ spl8_42
    | ~ spl8_88 ),
    inference(forward_demodulation,[],[f836,f308])).

fof(f836,plain,
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
    | ~ spl8_42
    | ~ spl8_88 ),
    inference(forward_demodulation,[],[f811,f352])).

fof(f811,plain,
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
    | ~ spl8_88 ),
    inference(resolution,[],[f680,f91])).

fof(f91,plain,(
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
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f680,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl8_88 ),
    inference(avatar_component_clause,[],[f678])).

fof(f835,plain,
    ( spl8_15
    | spl8_1
    | ~ spl8_84
    | ~ spl8_80
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
    | ~ spl8_32
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_41
    | ~ spl8_42
    | ~ spl8_88 ),
    inference(avatar_split_clause,[],[f834,f678,f351,f347,f322,f317,f279,f120,f100,f110,f105,f125,f120,f140,f135,f130,f155,f150,f145,f630,f654,f95,f164])).

fof(f164,plain,
    ( spl8_15
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f834,plain,
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
    | ~ spl8_32
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_41
    | ~ spl8_42
    | ~ spl8_88 ),
    inference(trivial_inequality_removal,[],[f833])).

fof(f833,plain,
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
    | ~ spl8_32
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_41
    | ~ spl8_42
    | ~ spl8_88 ),
    inference(forward_demodulation,[],[f832,f319])).

fof(f832,plain,
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
    | ~ spl8_32
    | ~ spl8_37
    | ~ spl8_41
    | ~ spl8_42
    | ~ spl8_88 ),
    inference(forward_demodulation,[],[f831,f324])).

fof(f831,plain,
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
    | ~ spl8_32
    | ~ spl8_41
    | ~ spl8_42
    | ~ spl8_88 ),
    inference(forward_demodulation,[],[f830,f348])).

fof(f830,plain,
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
    | ~ spl8_32
    | ~ spl8_42
    | ~ spl8_88 ),
    inference(forward_demodulation,[],[f829,f281])).

fof(f829,plain,
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
    | ~ spl8_42
    | ~ spl8_88 ),
    inference(forward_demodulation,[],[f828,f308])).

fof(f828,plain,
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
    | ~ spl8_42
    | ~ spl8_88 ),
    inference(forward_demodulation,[],[f810,f352])).

fof(f810,plain,
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
    | ~ spl8_88 ),
    inference(resolution,[],[f680,f92])).

fof(f92,plain,(
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
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
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

fof(f681,plain,
    ( spl8_88
    | ~ spl8_10
    | ~ spl8_9
    | ~ spl8_8
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f676,f591,f130,f135,f140,f678])).

fof(f591,plain,
    ( spl8_74
  <=> ! [X1] :
        ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f676,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl8_8
    | ~ spl8_74 ),
    inference(resolution,[],[f592,f132])).

fof(f132,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f592,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) )
    | ~ spl8_74 ),
    inference(avatar_component_clause,[],[f591])).

fof(f657,plain,
    ( spl8_84
    | ~ spl8_10
    | ~ spl8_9
    | ~ spl8_8
    | ~ spl8_70 ),
    inference(avatar_split_clause,[],[f652,f571,f130,f135,f140,f654])).

fof(f571,plain,
    ( spl8_70
  <=> ! [X1] :
        ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f652,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl8_8
    | ~ spl8_70 ),
    inference(resolution,[],[f572,f132])).

fof(f572,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) )
    | ~ spl8_70 ),
    inference(avatar_component_clause,[],[f571])).

fof(f633,plain,
    ( spl8_80
    | ~ spl8_10
    | ~ spl8_9
    | ~ spl8_8
    | ~ spl8_62 ),
    inference(avatar_split_clause,[],[f628,f524,f130,f135,f140,f630])).

fof(f524,plain,
    ( spl8_62
  <=> ! [X1] :
        ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f628,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl8_8
    | ~ spl8_62 ),
    inference(resolution,[],[f525,f132])).

fof(f525,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) )
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f524])).

fof(f593,plain,
    ( ~ spl8_6
    | ~ spl8_12
    | spl8_7
    | ~ spl8_13
    | spl8_2
    | spl8_74
    | ~ spl8_11
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f585,f414,f145,f591,f100,f155,f125,f150,f120])).

fof(f414,plain,
    ( spl8_52
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
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f585,plain,
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
    | ~ spl8_52 ),
    inference(resolution,[],[f415,f147])).

fof(f147,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f145])).

fof(f415,plain,
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
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f414])).

fof(f573,plain,
    ( ~ spl8_6
    | ~ spl8_12
    | spl8_7
    | ~ spl8_13
    | spl8_2
    | spl8_70
    | ~ spl8_11
    | ~ spl8_49 ),
    inference(avatar_split_clause,[],[f565,f393,f145,f571,f100,f155,f125,f150,f120])).

fof(f393,plain,
    ( spl8_49
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
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f565,plain,
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
    | ~ spl8_49 ),
    inference(resolution,[],[f394,f147])).

fof(f394,plain,
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
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f393])).

fof(f526,plain,
    ( ~ spl8_6
    | ~ spl8_12
    | spl8_7
    | ~ spl8_13
    | spl8_2
    | spl8_62
    | ~ spl8_11
    | ~ spl8_45 ),
    inference(avatar_split_clause,[],[f518,f371,f145,f524,f100,f155,f125,f150,f120])).

fof(f371,plain,
    ( spl8_45
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
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

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
    | ~ spl8_11
    | ~ spl8_45 ),
    inference(resolution,[],[f372,f147])).

fof(f372,plain,
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
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f371])).

fof(f416,plain,
    ( spl8_1
    | spl8_4
    | spl8_52
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f409,f105,f414,f110,f95])).

fof(f409,plain,
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
    | ~ spl8_3 ),
    inference(resolution,[],[f85,f107])).

fof(f107,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f395,plain,
    ( spl8_1
    | spl8_4
    | spl8_49
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f388,f105,f393,f110,f95])).

fof(f388,plain,
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
    | ~ spl8_3 ),
    inference(resolution,[],[f84,f107])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f373,plain,
    ( spl8_1
    | spl8_4
    | spl8_45
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f366,f105,f371,f110,f95])).

fof(f366,plain,
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
    | ~ spl8_3 ),
    inference(resolution,[],[f83,f107])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f353,plain,
    ( spl8_42
    | ~ spl8_13
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f345,f145,f155,f351])).

fof(f345,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK5)
        | k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1) )
    | ~ spl8_11 ),
    inference(resolution,[],[f82,f147])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f349,plain,
    ( spl8_41
    | ~ spl8_10
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f344,f130,f140,f347])).

fof(f344,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) )
    | ~ spl8_8 ),
    inference(resolution,[],[f82,f132])).

fof(f325,plain,
    ( spl8_37
    | ~ spl8_17
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f315,f206,f173,f322])).

fof(f173,plain,
    ( spl8_17
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f206,plain,
    ( spl8_23
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f315,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl8_17
    | ~ spl8_23 ),
    inference(resolution,[],[f301,f208])).

fof(f208,plain,
    ( v1_relat_1(sK5)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f206])).

fof(f301,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) )
    | ~ spl8_17 ),
    inference(resolution,[],[f62,f245])).

fof(f245,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl8_17 ),
    inference(resolution,[],[f238,f175])).

fof(f175,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f173])).

fof(f238,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f70,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f320,plain,
    ( spl8_36
    | ~ spl8_17
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f314,f197,f173,f317])).

fof(f197,plain,
    ( spl8_21
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f314,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl8_17
    | ~ spl8_21 ),
    inference(resolution,[],[f301,f199])).

fof(f199,plain,
    ( v1_relat_1(sK4)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f197])).

fof(f282,plain,
    ( spl8_32
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f276,f271,f279])).

fof(f271,plain,
    ( spl8_31
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f276,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl8_31 ),
    inference(resolution,[],[f273,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f79,f68])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f273,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f271])).

fof(f274,plain,
    ( spl8_31
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f269,f115,f271])).

fof(f115,plain,
    ( spl8_5
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f269,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl8_5 ),
    inference(resolution,[],[f268,f117])).

fof(f117,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f268,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(global_subsumption,[],[f241,f267])).

fof(f267,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1) ) ),
    inference(global_subsumption,[],[f238,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f241,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f71,f66])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f240,plain,(
    spl8_24 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | spl8_24 ),
    inference(resolution,[],[f212,f67])).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f212,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
    | spl8_24 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl8_24
  <=> v1_relat_1(k2_zfmisc_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f215,plain,(
    spl8_22 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl8_22 ),
    inference(resolution,[],[f203,f67])).

fof(f203,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | spl8_22 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl8_22
  <=> v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f213,plain,
    ( spl8_23
    | ~ spl8_24
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f181,f145,f210,f206])).

fof(f181,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
    | v1_relat_1(sK5)
    | ~ spl8_11 ),
    inference(resolution,[],[f63,f147])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f204,plain,
    ( spl8_21
    | ~ spl8_22
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f180,f130,f201,f197])).

fof(f180,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | v1_relat_1(sK4)
    | ~ spl8_8 ),
    inference(resolution,[],[f63,f132])).

fof(f176,plain,(
    spl8_17 ),
    inference(avatar_split_clause,[],[f58,f173])).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f171,plain,
    ( ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f44,f168,f164,f160])).

fof(f44,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f24])).

% (13823)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (13834)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (13832)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (13822)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f158,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f45,f155])).

fof(f45,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f153,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f46,f150])).

fof(f46,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f148,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f47,f145])).

fof(f47,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f143,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f48,f140])).

fof(f48,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f138,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f49,f135])).

fof(f49,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f133,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f50,f130])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f128,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f51,f125])).

fof(f51,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f123,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f52,f120])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f118,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f53,f115])).

fof(f53,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f113,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f54,f110])).

fof(f54,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f108,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f55,f105])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f103,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f56,f100])).

fof(f56,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f98,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f57,f95])).

fof(f57,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:44:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (13809)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (13824)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (13817)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (13816)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (13820)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (13828)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (13818)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (13810)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (13812)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (13808)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (13819)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (13811)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (13836)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (13837)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (13829)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (13835)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (13814)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (13821)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (13815)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (13833)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (13825)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (13827)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (13826)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (13825)Refutation not found, incomplete strategy% (13825)------------------------------
% 0.22/0.56  % (13825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (13825)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (13825)Memory used [KB]: 10746
% 0.22/0.56  % (13825)Time elapsed: 0.151 s
% 0.22/0.56  % (13825)------------------------------
% 0.22/0.56  % (13825)------------------------------
% 0.22/0.56  % (13813)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.56  % (13831)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.57  % (13830)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.57  % (13824)Refutation found. Thanks to Tanya!
% 1.38/0.57  % SZS status Theorem for theBenchmark
% 1.38/0.57  % SZS output start Proof for theBenchmark
% 1.38/0.57  fof(f934,plain,(
% 1.38/0.57    $false),
% 1.38/0.57    inference(avatar_sat_refutation,[],[f98,f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f153,f158,f171,f176,f204,f213,f215,f240,f274,f282,f320,f325,f349,f353,f373,f395,f416,f526,f573,f593,f633,f657,f681,f835,f843,f933])).
% 1.38/0.57  fof(f933,plain,(
% 1.38/0.57    ~spl8_36 | ~spl8_6 | spl8_16 | ~spl8_32 | ~spl8_37 | ~spl8_41 | ~spl8_42),
% 1.38/0.57    inference(avatar_split_clause,[],[f932,f351,f347,f322,f279,f168,f120,f317])).
% 1.38/0.57  fof(f317,plain,(
% 1.38/0.57    spl8_36 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 1.38/0.57  fof(f120,plain,(
% 1.38/0.57    spl8_6 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.38/0.57  fof(f168,plain,(
% 1.38/0.57    spl8_16 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.38/0.57  fof(f279,plain,(
% 1.38/0.57    spl8_32 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 1.38/0.57  fof(f322,plain,(
% 1.38/0.57    spl8_37 <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 1.38/0.57  fof(f347,plain,(
% 1.38/0.57    spl8_41 <=> ! [X0] : k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 1.38/0.57  fof(f351,plain,(
% 1.38/0.57    spl8_42 <=> ! [X1] : k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 1.38/0.57  fof(f932,plain,(
% 1.38/0.57    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | (~spl8_6 | spl8_16 | ~spl8_32 | ~spl8_37 | ~spl8_41 | ~spl8_42)),
% 1.38/0.57    inference(forward_demodulation,[],[f931,f324])).
% 1.38/0.57  fof(f324,plain,(
% 1.38/0.57    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | ~spl8_37),
% 1.38/0.57    inference(avatar_component_clause,[],[f322])).
% 1.38/0.57  fof(f931,plain,(
% 1.38/0.57    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | (~spl8_6 | spl8_16 | ~spl8_32 | ~spl8_41 | ~spl8_42)),
% 1.38/0.57    inference(forward_demodulation,[],[f930,f348])).
% 1.38/0.57  fof(f348,plain,(
% 1.38/0.57    ( ! [X0] : (k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)) ) | ~spl8_41),
% 1.38/0.57    inference(avatar_component_clause,[],[f347])).
% 1.38/0.57  fof(f930,plain,(
% 1.38/0.57    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (~spl8_6 | spl8_16 | ~spl8_32 | ~spl8_42)),
% 1.38/0.57    inference(forward_demodulation,[],[f929,f281])).
% 1.38/0.57  fof(f281,plain,(
% 1.38/0.57    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl8_32),
% 1.38/0.57    inference(avatar_component_clause,[],[f279])).
% 1.38/0.57  fof(f929,plain,(
% 1.38/0.57    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | (~spl8_6 | spl8_16 | ~spl8_42)),
% 1.38/0.57    inference(forward_demodulation,[],[f928,f308])).
% 1.38/0.57  fof(f308,plain,(
% 1.38/0.57    ( ! [X1] : (k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))) ) | ~spl8_6),
% 1.38/0.57    inference(resolution,[],[f88,f122])).
% 1.38/0.57  fof(f122,plain,(
% 1.38/0.57    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl8_6),
% 1.38/0.57    inference(avatar_component_clause,[],[f120])).
% 1.38/0.57  fof(f88,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 1.38/0.57    inference(definition_unfolding,[],[f80,f68])).
% 1.38/0.57  fof(f68,plain,(
% 1.38/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f8])).
% 1.38/0.57  fof(f8,axiom,(
% 1.38/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.38/0.57  fof(f80,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f38])).
% 1.38/0.57  fof(f38,plain,(
% 1.38/0.57    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.38/0.57    inference(ennf_transformation,[],[f6])).
% 1.38/0.57  fof(f6,axiom,(
% 1.38/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.38/0.57  fof(f928,plain,(
% 1.38/0.57    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (spl8_16 | ~spl8_42)),
% 1.38/0.57    inference(forward_demodulation,[],[f170,f352])).
% 1.38/0.57  fof(f352,plain,(
% 1.38/0.57    ( ! [X1] : (k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1)) ) | ~spl8_42),
% 1.38/0.57    inference(avatar_component_clause,[],[f351])).
% 1.38/0.57  fof(f170,plain,(
% 1.38/0.57    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl8_16),
% 1.38/0.57    inference(avatar_component_clause,[],[f168])).
% 1.38/0.57  fof(f843,plain,(
% 1.38/0.57    spl8_14 | spl8_1 | ~spl8_84 | ~spl8_80 | ~spl8_11 | ~spl8_12 | ~spl8_13 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_6 | spl8_7 | ~spl8_3 | spl8_4 | spl8_2 | ~spl8_6 | ~spl8_32 | ~spl8_36 | ~spl8_37 | ~spl8_41 | ~spl8_42 | ~spl8_88),
% 1.38/0.57    inference(avatar_split_clause,[],[f842,f678,f351,f347,f322,f317,f279,f120,f100,f110,f105,f125,f120,f140,f135,f130,f155,f150,f145,f630,f654,f95,f160])).
% 1.38/0.57  fof(f160,plain,(
% 1.38/0.57    spl8_14 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.38/0.57  fof(f95,plain,(
% 1.38/0.57    spl8_1 <=> v1_xboole_0(sK0)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.38/0.57  fof(f654,plain,(
% 1.38/0.57    spl8_84 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).
% 1.38/0.57  fof(f630,plain,(
% 1.38/0.57    spl8_80 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).
% 1.38/0.57  fof(f145,plain,(
% 1.38/0.57    spl8_11 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.38/0.57  fof(f150,plain,(
% 1.38/0.57    spl8_12 <=> v1_funct_2(sK5,sK3,sK1)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.38/0.57  fof(f155,plain,(
% 1.38/0.57    spl8_13 <=> v1_funct_1(sK5)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.38/0.57  fof(f130,plain,(
% 1.38/0.57    spl8_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.38/0.57  fof(f135,plain,(
% 1.38/0.57    spl8_9 <=> v1_funct_2(sK4,sK2,sK1)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.38/0.57  fof(f140,plain,(
% 1.38/0.57    spl8_10 <=> v1_funct_1(sK4)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.38/0.57  fof(f125,plain,(
% 1.38/0.57    spl8_7 <=> v1_xboole_0(sK3)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.38/0.57  fof(f105,plain,(
% 1.38/0.57    spl8_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.38/0.57  fof(f110,plain,(
% 1.38/0.57    spl8_4 <=> v1_xboole_0(sK2)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.38/0.57  fof(f100,plain,(
% 1.38/0.57    spl8_2 <=> v1_xboole_0(sK1)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.38/0.57  fof(f678,plain,(
% 1.38/0.57    spl8_88 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).
% 1.38/0.57  fof(f842,plain,(
% 1.38/0.57    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl8_6 | ~spl8_32 | ~spl8_36 | ~spl8_37 | ~spl8_41 | ~spl8_42 | ~spl8_88)),
% 1.38/0.57    inference(trivial_inequality_removal,[],[f841])).
% 1.38/0.57  fof(f841,plain,(
% 1.38/0.57    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl8_6 | ~spl8_32 | ~spl8_36 | ~spl8_37 | ~spl8_41 | ~spl8_42 | ~spl8_88)),
% 1.38/0.57    inference(forward_demodulation,[],[f840,f319])).
% 1.38/0.57  fof(f319,plain,(
% 1.38/0.57    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl8_36),
% 1.38/0.57    inference(avatar_component_clause,[],[f317])).
% 1.38/0.57  fof(f840,plain,(
% 1.38/0.57    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl8_6 | ~spl8_32 | ~spl8_37 | ~spl8_41 | ~spl8_42 | ~spl8_88)),
% 1.38/0.57    inference(forward_demodulation,[],[f839,f324])).
% 1.38/0.57  fof(f839,plain,(
% 1.38/0.57    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl8_6 | ~spl8_32 | ~spl8_41 | ~spl8_42 | ~spl8_88)),
% 1.38/0.57    inference(forward_demodulation,[],[f838,f348])).
% 1.38/0.57  fof(f838,plain,(
% 1.38/0.57    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl8_6 | ~spl8_32 | ~spl8_42 | ~spl8_88)),
% 1.38/0.57    inference(forward_demodulation,[],[f837,f281])).
% 1.38/0.57  fof(f837,plain,(
% 1.38/0.57    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl8_6 | ~spl8_42 | ~spl8_88)),
% 1.38/0.57    inference(forward_demodulation,[],[f836,f308])).
% 1.38/0.57  fof(f836,plain,(
% 1.38/0.57    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl8_42 | ~spl8_88)),
% 1.38/0.57    inference(forward_demodulation,[],[f811,f352])).
% 1.38/0.57  fof(f811,plain,(
% 1.38/0.57    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~spl8_88),
% 1.38/0.57    inference(resolution,[],[f680,f91])).
% 1.38/0.57  fof(f91,plain,(
% 1.38/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 1.38/0.57    inference(equality_resolution,[],[f60])).
% 1.38/0.57  fof(f60,plain,(
% 1.38/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.38/0.57    inference(cnf_transformation,[],[f26])).
% 1.38/0.57  fof(f26,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.38/0.57    inference(flattening,[],[f25])).
% 1.38/0.57  fof(f25,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.38/0.57    inference(ennf_transformation,[],[f17])).
% 1.38/0.57  fof(f17,axiom,(
% 1.38/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).
% 1.38/0.57  fof(f680,plain,(
% 1.38/0.57    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl8_88),
% 1.38/0.57    inference(avatar_component_clause,[],[f678])).
% 1.38/0.57  fof(f835,plain,(
% 1.38/0.57    spl8_15 | spl8_1 | ~spl8_84 | ~spl8_80 | ~spl8_11 | ~spl8_12 | ~spl8_13 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_6 | spl8_7 | ~spl8_3 | spl8_4 | spl8_2 | ~spl8_6 | ~spl8_32 | ~spl8_36 | ~spl8_37 | ~spl8_41 | ~spl8_42 | ~spl8_88),
% 1.38/0.57    inference(avatar_split_clause,[],[f834,f678,f351,f347,f322,f317,f279,f120,f100,f110,f105,f125,f120,f140,f135,f130,f155,f150,f145,f630,f654,f95,f164])).
% 1.38/0.57  fof(f164,plain,(
% 1.38/0.57    spl8_15 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.38/0.57  fof(f834,plain,(
% 1.38/0.57    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl8_6 | ~spl8_32 | ~spl8_36 | ~spl8_37 | ~spl8_41 | ~spl8_42 | ~spl8_88)),
% 1.38/0.57    inference(trivial_inequality_removal,[],[f833])).
% 1.38/0.57  fof(f833,plain,(
% 1.38/0.57    k1_xboole_0 != k1_xboole_0 | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl8_6 | ~spl8_32 | ~spl8_36 | ~spl8_37 | ~spl8_41 | ~spl8_42 | ~spl8_88)),
% 1.38/0.57    inference(forward_demodulation,[],[f832,f319])).
% 1.38/0.57  fof(f832,plain,(
% 1.38/0.57    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl8_6 | ~spl8_32 | ~spl8_37 | ~spl8_41 | ~spl8_42 | ~spl8_88)),
% 1.38/0.57    inference(forward_demodulation,[],[f831,f324])).
% 1.38/0.57  fof(f831,plain,(
% 1.38/0.57    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl8_6 | ~spl8_32 | ~spl8_41 | ~spl8_42 | ~spl8_88)),
% 1.38/0.57    inference(forward_demodulation,[],[f830,f348])).
% 1.38/0.57  fof(f830,plain,(
% 1.38/0.57    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl8_6 | ~spl8_32 | ~spl8_42 | ~spl8_88)),
% 1.38/0.57    inference(forward_demodulation,[],[f829,f281])).
% 1.38/0.57  fof(f829,plain,(
% 1.38/0.57    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl8_6 | ~spl8_42 | ~spl8_88)),
% 1.38/0.57    inference(forward_demodulation,[],[f828,f308])).
% 1.38/0.57  fof(f828,plain,(
% 1.38/0.57    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl8_42 | ~spl8_88)),
% 1.38/0.57    inference(forward_demodulation,[],[f810,f352])).
% 1.38/0.57  fof(f810,plain,(
% 1.38/0.57    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~spl8_88),
% 1.38/0.57    inference(resolution,[],[f680,f92])).
% 1.38/0.57  fof(f92,plain,(
% 1.38/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 1.38/0.57    inference(equality_resolution,[],[f59])).
% 1.38/0.57  fof(f59,plain,(
% 1.38/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.38/0.57    inference(cnf_transformation,[],[f26])).
% 1.38/0.57  fof(f681,plain,(
% 1.38/0.57    spl8_88 | ~spl8_10 | ~spl8_9 | ~spl8_8 | ~spl8_74),
% 1.38/0.57    inference(avatar_split_clause,[],[f676,f591,f130,f135,f140,f678])).
% 1.38/0.57  fof(f591,plain,(
% 1.38/0.57    spl8_74 <=> ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).
% 1.38/0.57  fof(f676,plain,(
% 1.38/0.57    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl8_8 | ~spl8_74)),
% 1.38/0.57    inference(resolution,[],[f592,f132])).
% 1.38/0.57  fof(f132,plain,(
% 1.38/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl8_8),
% 1.38/0.57    inference(avatar_component_clause,[],[f130])).
% 1.38/0.57  fof(f592,plain,(
% 1.38/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))) ) | ~spl8_74),
% 1.38/0.57    inference(avatar_component_clause,[],[f591])).
% 1.38/0.57  fof(f657,plain,(
% 1.38/0.57    spl8_84 | ~spl8_10 | ~spl8_9 | ~spl8_8 | ~spl8_70),
% 1.38/0.57    inference(avatar_split_clause,[],[f652,f571,f130,f135,f140,f654])).
% 1.38/0.57  fof(f571,plain,(
% 1.38/0.57    spl8_70 <=> ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).
% 1.38/0.57  fof(f652,plain,(
% 1.38/0.57    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl8_8 | ~spl8_70)),
% 1.38/0.57    inference(resolution,[],[f572,f132])).
% 1.38/0.57  fof(f572,plain,(
% 1.38/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1)) ) | ~spl8_70),
% 1.38/0.57    inference(avatar_component_clause,[],[f571])).
% 1.38/0.57  fof(f633,plain,(
% 1.38/0.57    spl8_80 | ~spl8_10 | ~spl8_9 | ~spl8_8 | ~spl8_62),
% 1.38/0.57    inference(avatar_split_clause,[],[f628,f524,f130,f135,f140,f630])).
% 1.38/0.57  fof(f524,plain,(
% 1.38/0.57    spl8_62 <=> ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).
% 1.38/0.57  fof(f628,plain,(
% 1.38/0.57    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl8_8 | ~spl8_62)),
% 1.38/0.57    inference(resolution,[],[f525,f132])).
% 1.38/0.57  fof(f525,plain,(
% 1.38/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5))) ) | ~spl8_62),
% 1.38/0.58    inference(avatar_component_clause,[],[f524])).
% 1.38/0.58  fof(f593,plain,(
% 1.38/0.58    ~spl8_6 | ~spl8_12 | spl8_7 | ~spl8_13 | spl8_2 | spl8_74 | ~spl8_11 | ~spl8_52),
% 1.38/0.58    inference(avatar_split_clause,[],[f585,f414,f145,f591,f100,f155,f125,f150,f120])).
% 1.38/0.58  fof(f414,plain,(
% 1.38/0.58    spl8_52 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 1.38/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).
% 1.38/0.58  fof(f585,plain,(
% 1.38/0.58    ( ! [X1] : (m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl8_11 | ~spl8_52)),
% 1.38/0.58    inference(resolution,[],[f415,f147])).
% 1.38/0.58  fof(f147,plain,(
% 1.38/0.58    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl8_11),
% 1.38/0.58    inference(avatar_component_clause,[],[f145])).
% 1.38/0.58  fof(f415,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0))) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl8_52),
% 1.38/0.58    inference(avatar_component_clause,[],[f414])).
% 1.38/0.58  fof(f573,plain,(
% 1.38/0.58    ~spl8_6 | ~spl8_12 | spl8_7 | ~spl8_13 | spl8_2 | spl8_70 | ~spl8_11 | ~spl8_49),
% 1.38/0.58    inference(avatar_split_clause,[],[f565,f393,f145,f571,f100,f155,f125,f150,f120])).
% 1.38/0.58  fof(f393,plain,(
% 1.38/0.58    spl8_49 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 1.38/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 1.38/0.58  fof(f565,plain,(
% 1.38/0.58    ( ! [X1] : (v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl8_11 | ~spl8_49)),
% 1.38/0.58    inference(resolution,[],[f394,f147])).
% 1.38/0.58  fof(f394,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl8_49),
% 1.38/0.58    inference(avatar_component_clause,[],[f393])).
% 1.38/0.58  fof(f526,plain,(
% 1.38/0.58    ~spl8_6 | ~spl8_12 | spl8_7 | ~spl8_13 | spl8_2 | spl8_62 | ~spl8_11 | ~spl8_45),
% 1.38/0.58    inference(avatar_split_clause,[],[f518,f371,f145,f524,f100,f155,f125,f150,f120])).
% 1.38/0.58  fof(f371,plain,(
% 1.38/0.58    spl8_45 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)))),
% 1.38/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 1.38/0.58  fof(f518,plain,(
% 1.38/0.58    ( ! [X1] : (v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5)) | v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | v1_xboole_0(sK3) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))) ) | (~spl8_11 | ~spl8_45)),
% 1.38/0.58    inference(resolution,[],[f372,f147])).
% 1.38/0.58  fof(f372,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3)) | v1_xboole_0(X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) ) | ~spl8_45),
% 1.38/0.58    inference(avatar_component_clause,[],[f371])).
% 1.38/0.58  fof(f416,plain,(
% 1.38/0.58    spl8_1 | spl8_4 | spl8_52 | ~spl8_3),
% 1.38/0.58    inference(avatar_split_clause,[],[f409,f105,f414,f110,f95])).
% 1.38/0.58  fof(f409,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X1),X0)))) ) | ~spl8_3),
% 1.38/0.58    inference(resolution,[],[f85,f107])).
% 1.38/0.58  fof(f107,plain,(
% 1.38/0.58    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl8_3),
% 1.38/0.58    inference(avatar_component_clause,[],[f105])).
% 1.38/0.58  fof(f85,plain,(
% 1.38/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 1.38/0.58    inference(cnf_transformation,[],[f43])).
% 1.38/0.58  fof(f43,plain,(
% 1.38/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.38/0.58    inference(flattening,[],[f42])).
% 1.38/0.58  fof(f42,plain,(
% 1.38/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.38/0.58    inference(ennf_transformation,[],[f18])).
% 1.38/0.58  fof(f18,axiom,(
% 1.38/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 1.38/0.58  fof(f395,plain,(
% 1.38/0.58    spl8_1 | spl8_4 | spl8_49 | ~spl8_3),
% 1.38/0.58    inference(avatar_split_clause,[],[f388,f105,f393,f110,f95])).
% 1.38/0.58  fof(f388,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(k1_tmap_1(sK0,X0,sK2,X1,X2,X3),k4_subset_1(sK0,sK2,X1),X0)) ) | ~spl8_3),
% 1.38/0.58    inference(resolution,[],[f84,f107])).
% 1.38/0.58  fof(f84,plain,(
% 1.38/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f43])).
% 1.38/0.58  fof(f373,plain,(
% 1.38/0.58    spl8_1 | spl8_4 | spl8_45 | ~spl8_3),
% 1.38/0.58    inference(avatar_split_clause,[],[f366,f105,f371,f110,f95])).
% 1.38/0.58  fof(f366,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_1(k1_tmap_1(sK0,X0,sK2,X1,X2,X3))) ) | ~spl8_3),
% 1.38/0.58    inference(resolution,[],[f83,f107])).
% 1.38/0.58  fof(f83,plain,(
% 1.38/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 1.38/0.58    inference(cnf_transformation,[],[f43])).
% 1.38/0.58  fof(f353,plain,(
% 1.38/0.58    spl8_42 | ~spl8_13 | ~spl8_11),
% 1.38/0.58    inference(avatar_split_clause,[],[f345,f145,f155,f351])).
% 1.38/0.58  fof(f345,plain,(
% 1.38/0.58    ( ! [X1] : (~v1_funct_1(sK5) | k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1)) ) | ~spl8_11),
% 1.38/0.58    inference(resolution,[],[f82,f147])).
% 1.38/0.58  fof(f82,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f41])).
% 1.38/0.58  fof(f41,plain,(
% 1.38/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.38/0.58    inference(flattening,[],[f40])).
% 1.38/0.58  fof(f40,plain,(
% 1.38/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.38/0.58    inference(ennf_transformation,[],[f16])).
% 1.38/0.58  fof(f16,axiom,(
% 1.38/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.38/0.58  fof(f349,plain,(
% 1.38/0.58    spl8_41 | ~spl8_10 | ~spl8_8),
% 1.38/0.58    inference(avatar_split_clause,[],[f344,f130,f140,f347])).
% 1.38/0.58  fof(f344,plain,(
% 1.38/0.58    ( ! [X0] : (~v1_funct_1(sK4) | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)) ) | ~spl8_8),
% 1.38/0.58    inference(resolution,[],[f82,f132])).
% 1.38/0.58  fof(f325,plain,(
% 1.38/0.58    spl8_37 | ~spl8_17 | ~spl8_23),
% 1.38/0.58    inference(avatar_split_clause,[],[f315,f206,f173,f322])).
% 1.38/0.58  fof(f173,plain,(
% 1.38/0.58    spl8_17 <=> v1_xboole_0(k1_xboole_0)),
% 1.38/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.38/0.58  fof(f206,plain,(
% 1.38/0.58    spl8_23 <=> v1_relat_1(sK5)),
% 1.38/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 1.38/0.58  fof(f315,plain,(
% 1.38/0.58    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | (~spl8_17 | ~spl8_23)),
% 1.38/0.58    inference(resolution,[],[f301,f208])).
% 1.38/0.58  fof(f208,plain,(
% 1.38/0.58    v1_relat_1(sK5) | ~spl8_23),
% 1.38/0.58    inference(avatar_component_clause,[],[f206])).
% 1.38/0.58  fof(f301,plain,(
% 1.38/0.58    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)) ) | ~spl8_17),
% 1.38/0.58    inference(resolution,[],[f62,f245])).
% 1.38/0.58  fof(f245,plain,(
% 1.38/0.58    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | ~spl8_17),
% 1.38/0.58    inference(resolution,[],[f238,f175])).
% 1.38/0.58  fof(f175,plain,(
% 1.38/0.58    v1_xboole_0(k1_xboole_0) | ~spl8_17),
% 1.38/0.58    inference(avatar_component_clause,[],[f173])).
% 1.38/0.58  fof(f238,plain,(
% 1.38/0.58    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_xboole_0(X0,X1)) )),
% 1.38/0.58    inference(resolution,[],[f70,f66])).
% 1.38/0.58  fof(f66,plain,(
% 1.38/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f1])).
% 1.38/0.58  fof(f1,axiom,(
% 1.38/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.38/0.58  fof(f70,plain,(
% 1.38/0.58    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f30])).
% 1.38/0.58  fof(f30,plain,(
% 1.38/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.38/0.58    inference(ennf_transformation,[],[f21])).
% 1.38/0.58  fof(f21,plain,(
% 1.38/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.38/0.58    inference(rectify,[],[f5])).
% 1.38/0.58  fof(f5,axiom,(
% 1.38/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.38/0.58  fof(f62,plain,(
% 1.38/0.58    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f27])).
% 1.38/0.58  fof(f27,plain,(
% 1.38/0.58    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.38/0.58    inference(ennf_transformation,[],[f11])).
% 1.38/0.58  fof(f11,axiom,(
% 1.38/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 1.38/0.58  fof(f320,plain,(
% 1.38/0.58    spl8_36 | ~spl8_17 | ~spl8_21),
% 1.38/0.58    inference(avatar_split_clause,[],[f314,f197,f173,f317])).
% 1.38/0.58  fof(f197,plain,(
% 1.38/0.58    spl8_21 <=> v1_relat_1(sK4)),
% 1.38/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.38/0.58  fof(f314,plain,(
% 1.38/0.58    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | (~spl8_17 | ~spl8_21)),
% 1.38/0.58    inference(resolution,[],[f301,f199])).
% 1.38/0.58  fof(f199,plain,(
% 1.38/0.58    v1_relat_1(sK4) | ~spl8_21),
% 1.38/0.58    inference(avatar_component_clause,[],[f197])).
% 1.38/0.58  fof(f282,plain,(
% 1.38/0.58    spl8_32 | ~spl8_31),
% 1.38/0.58    inference(avatar_split_clause,[],[f276,f271,f279])).
% 1.38/0.58  fof(f271,plain,(
% 1.38/0.58    spl8_31 <=> r1_xboole_0(sK2,sK3)),
% 1.38/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 1.38/0.58  fof(f276,plain,(
% 1.38/0.58    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl8_31),
% 1.38/0.58    inference(resolution,[],[f273,f86])).
% 1.38/0.58  fof(f86,plain,(
% 1.38/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.38/0.58    inference(definition_unfolding,[],[f79,f68])).
% 1.38/0.58  fof(f79,plain,(
% 1.38/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f2])).
% 1.38/0.58  fof(f2,axiom,(
% 1.38/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.38/0.58  fof(f273,plain,(
% 1.38/0.58    r1_xboole_0(sK2,sK3) | ~spl8_31),
% 1.38/0.58    inference(avatar_component_clause,[],[f271])).
% 1.38/0.58  fof(f274,plain,(
% 1.38/0.58    spl8_31 | ~spl8_5),
% 1.38/0.58    inference(avatar_split_clause,[],[f269,f115,f271])).
% 1.38/0.58  fof(f115,plain,(
% 1.38/0.58    spl8_5 <=> r1_subset_1(sK2,sK3)),
% 1.38/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.38/0.58  fof(f269,plain,(
% 1.38/0.58    r1_xboole_0(sK2,sK3) | ~spl8_5),
% 1.38/0.58    inference(resolution,[],[f268,f117])).
% 1.38/0.58  fof(f117,plain,(
% 1.38/0.58    r1_subset_1(sK2,sK3) | ~spl8_5),
% 1.38/0.58    inference(avatar_component_clause,[],[f115])).
% 1.38/0.58  fof(f268,plain,(
% 1.38/0.58    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | r1_xboole_0(X0,X1)) )),
% 1.38/0.58    inference(global_subsumption,[],[f241,f267])).
% 1.38/0.58  fof(f267,plain,(
% 1.38/0.58    ( ! [X0,X1] : (v1_xboole_0(X1) | r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1)) )),
% 1.38/0.58    inference(global_subsumption,[],[f238,f75])).
% 1.38/0.58  fof(f75,plain,(
% 1.38/0.58    ( ! [X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f35])).
% 1.38/0.58  fof(f35,plain,(
% 1.38/0.58    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.38/0.58    inference(flattening,[],[f34])).
% 1.38/0.58  fof(f34,plain,(
% 1.38/0.58    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.38/0.58    inference(ennf_transformation,[],[f12])).
% 1.38/0.58  fof(f12,axiom,(
% 1.38/0.58    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 1.38/0.58  fof(f241,plain,(
% 1.38/0.58    ( ! [X0,X1] : (~v1_xboole_0(X1) | r1_xboole_0(X0,X1)) )),
% 1.38/0.58    inference(resolution,[],[f71,f66])).
% 1.38/0.58  fof(f71,plain,(
% 1.38/0.58    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f30])).
% 1.38/0.58  fof(f240,plain,(
% 1.38/0.58    spl8_24),
% 1.38/0.58    inference(avatar_contradiction_clause,[],[f239])).
% 1.38/0.58  fof(f239,plain,(
% 1.38/0.58    $false | spl8_24),
% 1.38/0.58    inference(resolution,[],[f212,f67])).
% 1.38/0.58  fof(f67,plain,(
% 1.38/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.38/0.58    inference(cnf_transformation,[],[f10])).
% 1.38/0.58  fof(f10,axiom,(
% 1.38/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.38/0.58  fof(f212,plain,(
% 1.38/0.58    ~v1_relat_1(k2_zfmisc_1(sK3,sK1)) | spl8_24),
% 1.38/0.58    inference(avatar_component_clause,[],[f210])).
% 1.38/0.58  fof(f210,plain,(
% 1.38/0.58    spl8_24 <=> v1_relat_1(k2_zfmisc_1(sK3,sK1))),
% 1.38/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 1.38/0.58  fof(f215,plain,(
% 1.38/0.58    spl8_22),
% 1.38/0.58    inference(avatar_contradiction_clause,[],[f214])).
% 1.38/0.58  fof(f214,plain,(
% 1.38/0.58    $false | spl8_22),
% 1.38/0.58    inference(resolution,[],[f203,f67])).
% 1.38/0.58  fof(f203,plain,(
% 1.38/0.58    ~v1_relat_1(k2_zfmisc_1(sK2,sK1)) | spl8_22),
% 1.38/0.58    inference(avatar_component_clause,[],[f201])).
% 1.38/0.58  fof(f201,plain,(
% 1.38/0.58    spl8_22 <=> v1_relat_1(k2_zfmisc_1(sK2,sK1))),
% 1.38/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 1.38/0.58  fof(f213,plain,(
% 1.38/0.58    spl8_23 | ~spl8_24 | ~spl8_11),
% 1.38/0.58    inference(avatar_split_clause,[],[f181,f145,f210,f206])).
% 1.38/0.58  fof(f181,plain,(
% 1.38/0.58    ~v1_relat_1(k2_zfmisc_1(sK3,sK1)) | v1_relat_1(sK5) | ~spl8_11),
% 1.38/0.58    inference(resolution,[],[f63,f147])).
% 1.38/0.58  fof(f63,plain,(
% 1.38/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f28])).
% 1.38/0.58  fof(f28,plain,(
% 1.38/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.38/0.58    inference(ennf_transformation,[],[f9])).
% 1.38/0.58  fof(f9,axiom,(
% 1.38/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.38/0.58  fof(f204,plain,(
% 1.38/0.58    spl8_21 | ~spl8_22 | ~spl8_8),
% 1.38/0.58    inference(avatar_split_clause,[],[f180,f130,f201,f197])).
% 1.38/0.58  fof(f180,plain,(
% 1.38/0.58    ~v1_relat_1(k2_zfmisc_1(sK2,sK1)) | v1_relat_1(sK4) | ~spl8_8),
% 1.38/0.58    inference(resolution,[],[f63,f132])).
% 1.38/0.58  fof(f176,plain,(
% 1.38/0.58    spl8_17),
% 1.38/0.58    inference(avatar_split_clause,[],[f58,f173])).
% 1.38/0.58  fof(f58,plain,(
% 1.38/0.58    v1_xboole_0(k1_xboole_0)),
% 1.38/0.58    inference(cnf_transformation,[],[f3])).
% 1.38/0.58  fof(f3,axiom,(
% 1.38/0.58    v1_xboole_0(k1_xboole_0)),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.38/0.58  fof(f171,plain,(
% 1.38/0.58    ~spl8_14 | ~spl8_15 | ~spl8_16),
% 1.38/0.58    inference(avatar_split_clause,[],[f44,f168,f164,f160])).
% 1.38/0.58  fof(f44,plain,(
% 1.38/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.38/0.58    inference(cnf_transformation,[],[f24])).
% 1.38/0.58  % (13823)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.58  % (13834)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.58  % (13832)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.72/0.59  % (13822)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.72/0.60  fof(f24,plain,(
% 1.72/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.72/0.60    inference(flattening,[],[f23])).
% 1.72/0.60  fof(f23,plain,(
% 1.72/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.72/0.60    inference(ennf_transformation,[],[f20])).
% 1.72/0.60  fof(f20,negated_conjecture,(
% 1.72/0.60    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.72/0.60    inference(negated_conjecture,[],[f19])).
% 1.72/0.60  fof(f19,conjecture,(
% 1.72/0.60    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.72/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).
% 1.72/0.60  fof(f158,plain,(
% 1.72/0.60    spl8_13),
% 1.72/0.60    inference(avatar_split_clause,[],[f45,f155])).
% 1.72/0.60  fof(f45,plain,(
% 1.72/0.60    v1_funct_1(sK5)),
% 1.72/0.60    inference(cnf_transformation,[],[f24])).
% 1.72/0.60  fof(f153,plain,(
% 1.72/0.60    spl8_12),
% 1.72/0.60    inference(avatar_split_clause,[],[f46,f150])).
% 1.72/0.60  fof(f46,plain,(
% 1.72/0.60    v1_funct_2(sK5,sK3,sK1)),
% 1.72/0.60    inference(cnf_transformation,[],[f24])).
% 1.72/0.60  fof(f148,plain,(
% 1.72/0.60    spl8_11),
% 1.72/0.60    inference(avatar_split_clause,[],[f47,f145])).
% 1.72/0.60  fof(f47,plain,(
% 1.72/0.60    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.72/0.60    inference(cnf_transformation,[],[f24])).
% 1.72/0.60  fof(f143,plain,(
% 1.72/0.60    spl8_10),
% 1.72/0.60    inference(avatar_split_clause,[],[f48,f140])).
% 1.72/0.60  fof(f48,plain,(
% 1.72/0.60    v1_funct_1(sK4)),
% 1.72/0.60    inference(cnf_transformation,[],[f24])).
% 1.72/0.60  fof(f138,plain,(
% 1.72/0.60    spl8_9),
% 1.72/0.60    inference(avatar_split_clause,[],[f49,f135])).
% 1.72/0.60  fof(f49,plain,(
% 1.72/0.60    v1_funct_2(sK4,sK2,sK1)),
% 1.72/0.60    inference(cnf_transformation,[],[f24])).
% 1.72/0.60  fof(f133,plain,(
% 1.72/0.60    spl8_8),
% 1.72/0.60    inference(avatar_split_clause,[],[f50,f130])).
% 1.72/0.60  fof(f50,plain,(
% 1.72/0.60    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.72/0.60    inference(cnf_transformation,[],[f24])).
% 1.72/0.60  fof(f128,plain,(
% 1.72/0.60    ~spl8_7),
% 1.72/0.60    inference(avatar_split_clause,[],[f51,f125])).
% 1.72/0.60  fof(f51,plain,(
% 1.72/0.60    ~v1_xboole_0(sK3)),
% 1.72/0.60    inference(cnf_transformation,[],[f24])).
% 1.72/0.60  fof(f123,plain,(
% 1.72/0.60    spl8_6),
% 1.72/0.60    inference(avatar_split_clause,[],[f52,f120])).
% 1.72/0.60  fof(f52,plain,(
% 1.72/0.60    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.72/0.60    inference(cnf_transformation,[],[f24])).
% 1.72/0.60  fof(f118,plain,(
% 1.72/0.60    spl8_5),
% 1.72/0.60    inference(avatar_split_clause,[],[f53,f115])).
% 1.72/0.60  fof(f53,plain,(
% 1.72/0.60    r1_subset_1(sK2,sK3)),
% 1.72/0.60    inference(cnf_transformation,[],[f24])).
% 1.72/0.60  fof(f113,plain,(
% 1.72/0.60    ~spl8_4),
% 1.72/0.60    inference(avatar_split_clause,[],[f54,f110])).
% 1.72/0.60  fof(f54,plain,(
% 1.72/0.60    ~v1_xboole_0(sK2)),
% 1.72/0.60    inference(cnf_transformation,[],[f24])).
% 1.72/0.60  fof(f108,plain,(
% 1.72/0.60    spl8_3),
% 1.72/0.60    inference(avatar_split_clause,[],[f55,f105])).
% 1.72/0.60  fof(f55,plain,(
% 1.72/0.60    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.72/0.60    inference(cnf_transformation,[],[f24])).
% 1.72/0.60  fof(f103,plain,(
% 1.72/0.60    ~spl8_2),
% 1.72/0.60    inference(avatar_split_clause,[],[f56,f100])).
% 1.72/0.60  fof(f56,plain,(
% 1.72/0.60    ~v1_xboole_0(sK1)),
% 1.72/0.60    inference(cnf_transformation,[],[f24])).
% 1.72/0.60  fof(f98,plain,(
% 1.72/0.60    ~spl8_1),
% 1.72/0.60    inference(avatar_split_clause,[],[f57,f95])).
% 1.72/0.60  fof(f57,plain,(
% 1.72/0.60    ~v1_xboole_0(sK0)),
% 1.72/0.60    inference(cnf_transformation,[],[f24])).
% 1.72/0.60  % SZS output end Proof for theBenchmark
% 1.72/0.60  % (13824)------------------------------
% 1.72/0.60  % (13824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.60  % (13824)Termination reason: Refutation
% 1.72/0.60  
% 1.72/0.60  % (13824)Memory used [KB]: 11513
% 1.72/0.60  % (13824)Time elapsed: 0.148 s
% 1.72/0.60  % (13824)------------------------------
% 1.72/0.60  % (13824)------------------------------
% 1.72/0.60  % (13807)Success in time 0.236 s
%------------------------------------------------------------------------------
